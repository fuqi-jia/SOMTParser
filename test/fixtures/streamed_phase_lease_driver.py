"""Acquire only the capacity required by each complete, hash-bound phase."""
from contextlib import contextmanager
from pathlib import Path
import importlib.util
import os
import resource
import subprocess
import sys
import time
import traceback

import verified_spool as spool
from common import CONFIG, ROOT, ROWS, case, environment, verify


def main(index):
    directory=case(index)
    state=dict(index=index,id=ROWS[index]['id'],pid=os.getpid(),child_pids=[],complete=False,
               phase='waiting-both-slots',passed=False,limits=CONFIG['limits'],
               cli_sha256=CONFIG['cli_sha256'],original_results_unchanged=True,
               source_xz_sha256=ROWS[index]['inputs'][0]['sha256'],new_attempt=True)
    children=[]
    lease_event_index=0
    audit_errors=[]

    def audit_lease(event, stage, requested_slots):
        nonlocal lease_event_index
        paths={str(Path(CONFIG['slot_directory'])/f'{i}.lock') for i in range(2)}
        paths.add(CONFIG['writer_lock'])
        held={}
        for fd in Path('/proc/self/fd').iterdir():
            try:
                target=os.readlink(fd)
                if target in paths:
                    lines=Path('/proc/self/fdinfo',fd.name).read_text().splitlines()
                    locks=[line for line in lines if line.startswith('lock:')]
                    if locks:held[target]=locks
            except FileNotFoundError:
                continue
        spool.immutable(directory/'lease-audit'/f'{lease_event_index:03d}.json',
            dict(event=event, stage=stage, requested_slots=requested_slots,
                 pid=os.getpid(), observed_unix=time.time(), held_locks=held,
                 children=[dict(action=name,pid=child.pid,returncode=child.poll())
                           for name,child in children]))
        lease_event_index+=1

    def audit_without_masking_primary(event, stage, count):
        try:
            audit_lease(event, stage, count)
        except Exception as error:
            # Metadata errors cannot replace a converter/checker/receipt error.
            # A clean execution still refuses PASS if any audit was lost.
            audit_errors.append(dict(event=event,stage=stage,error=repr(error)))
            try:
                os.write(2, ('Lease audit failed: '+repr(error)+'\n').encode())
            except OSError:
                pass

    def save(**values):
        state.update(values,observed_unix=time.time())
        spool.atomic(directory/'state.json',state)

    def launch(action,*fds):
        log=(directory/(action+'.log')).open('xb')
        try:
            child=subprocess.Popen(['/usr/bin/time','-v',CONFIG['python'],'-B',str(ROOT/'worker.py'),
                action,str(index),*map(str,fds)],cwd=ROOT,env=environment(),pass_fds=fds,
                stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
        finally:
            log.close()
        children.append((action,child))
        return child

    def join_all():
        codes={name:child.wait() for name,child in children}
        children.clear()
        save(child_pids=[],worker_returncodes={**state.get('worker_returncodes',{}),**codes})
        return codes

    def record(name):
        path=directory/(name+'.json')
        return spool.read(path) if path.exists() else {}

    def require_no_harness_errors():
        failures={p.name:spool.read(p) for p in directory.glob('*-error.json')}
        assert not any(value.get('fatal_harness_error') for value in failures.values()),failures

    try:
        save(resource_limits=Path('/proc/self/limits').read_text())
        verify()
        spec=importlib.util.spec_from_file_location('slots',CONFIG['slot_helper'])
        slots=importlib.util.module_from_spec(spec);spec.loader.exec_module(slots)
        spec=importlib.util.spec_from_file_location('reservations',CONFIG['reservation_helper'])
        reservations=importlib.util.module_from_spec(spec);spec.loader.exec_module(reservations)
        @contextmanager
        def admitted(stage, count):
            # Waiting for a D receipt never consumes experiment capacity. Every
            # admitted child is reaped before its own phase releases the lease.
            save(phase='waiting-one-slot' if count==1 else 'waiting-both-slots',
                 admission_stage=stage, requested_slots=count)
            lease=(slots.experiment_slot(CONFIG['slot_directory'],CONFIG['writer_lock'],count=2)
                   if count==1 else
                   reservations.reserved_experiment_slots(CONFIG['slot_directory'],CONFIG['writer_lock'],count=2))
            try:
                with lease:
                    try:
                        audit_without_masking_primary('acquired',stage,count)
                        yield
                    finally:
                        interrupted=None
                        primary=sys.exc_info()[1]
                        for _,child in children:
                            while True:
                                try:
                                    child.wait()
                                    break
                                except InterruptedError:
                                    continue
                                except KeyboardInterrupt as error:
                                    # Defer Ctrl-C until admitted children exit.
                                    interrupted=error
                        audit_without_masking_primary('children-reaped-before-release',stage,count)
                        if interrupted is not None and primary is None:
                            raise interrupted
            finally:
                audit_without_masking_primary('released',stage,count)

        with admitted('export',2):
            save(phase='exporting-with-source-and-target-spools')
            source_read,source_write=os.pipe()
            target_read,target_write=os.pipe()
            try:
                launch('drain-export',target_read)
                launch('source-feed',source_write)
                launch('convert',source_read,target_write)
            finally:
                for descriptor in [source_read,source_write,target_read,target_write]:os.close(descriptor)
            save(child_pids=[p.pid for _,p in children])
            codes=join_all()
            require_no_harness_errors()
            translated,source,exported=record('translation'),record('source-feed'),record('export')
            converted=bool(all(code==0 for code in codes.values()) and translated.get('complete')
                and translated.get('translation_ok')
                and source.get('complete') and not source.get('broken_pipe') and exported.get('complete'))
            save(conversion_pass=converted)
            if not converted:
                save(complete=True,phase='conversion-failed',passed=False,
                     translation=translated,source_feed=source,export=exported)
                return
        audit_without_masking_primary('receipt-wait','full-D-receipt',0)
        save(phase='waiting-full-D-target-verification')
        receipt=directory/'D-target.json'
        while not receipt.exists():time.sleep(0.2)
        checked=spool.read(receipt)
        assert checked['verified'] and checked['full_gzip_EOF_verified']
        assert checked['gzip_sha256']==exported['target_gzip_sha256'] and checked['gzip_bytes']==exported['target_gzip_bytes']
        assert checked['raw_sha256']==exported['target_sha256'] and checked['raw_bytes']==exported['target_bytes']
        with admitted('envelope',1):
            save(phase='whole-target-envelope')
            launch('envelope')
            save(child_pids=[p.pid for _,p in children])
            envelope_codes=join_all()
            require_no_harness_errors()
            envelope=record('envelope')
        with admitted('whole-Optimize-load',2):
            save(phase='whole-independent-Optimize-load')
            target_read,target_write=os.pipe()
            try:
                launch('parse-feed',target_write)
                launch('parse',target_read)
            finally:
                os.close(target_read);os.close(target_write)
            save(child_pids=[p.pid for _,p in children])
            parse_codes=join_all()
            require_no_harness_errors()
        parsed,feed=record('parse'),record('parse-feed')
        whole_parse=bool(all(code==0 for code in parse_codes.values()) and parsed.get('parsed')
                         and feed.get('source_eof') and feed.get('raw_sha256')==exported['target_sha256'])
        exact=bool(envelope_codes['envelope']==0 and envelope.get('verified'))
        verify()
        assert not audit_errors, audit_errors
        save(complete=True,phase='complete',passed=converted and exact and whole_parse,
             conversion_pass=converted,full_envelope_pass=exact,
             independent_optimize_load_pass=whole_parse,
             whole_module_parse_pass=whole_parse and exact,
             complete_target_certificate_pass=exact,envelope=envelope,parse=parsed,
             parse_feed=feed,solver_status='not-run',
             proof_scope='Complete exact target envelope and independent whole Optimize load; source semantic equivalence not checked')
    except BaseException:
        save(complete=True,phase='harness-failed',passed=False,child_pids=[],
             exception=traceback.format_exc(),lease_audit_errors=audit_errors)
        raise


if __name__=='__main__':
    main(int(sys.argv[1]))
