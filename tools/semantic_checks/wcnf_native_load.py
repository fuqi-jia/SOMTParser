"""Stream every original WCNF SMT term through a compiled CVC5 load bridge.

This checks whole-module parsing and sorts, not source equivalence or weighted
cost. A complete original-stream semantic certificate must be checked separately.
The two child processes require two globally admitted leaves.
"""
from pathlib import Path
from contextlib import nullcontext
import argparse
import bz2
import gzip
import hashlib
import json
import lzma
import os
import subprocess
import threading


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def open_input(path):
    with Path(path).open('rb') as stream:
        magic = stream.read(6)
    opener = lzma.open if magic.startswith(b'\xfd7zXZ') else gzip.open if magic.startswith(b'\x1f\x8b') else bz2.open if magic.startswith(b'BZh') else open
    return opener(path, 'rb')


def load_whole(target, bridge_executable, cvc5, directory, spawn_guard=None):
    target = Path(target).resolve()
    bridge_executable = Path(bridge_executable).resolve()
    cvc5 = Path(cvc5).resolve()
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    native_sha, cvc5_sha = sha(bridge_executable), sha(cvc5)
    row = dict(passed=False, whole_module_loading_performed=False,
               source_relation_checked=False, weighted_cost_checked=False,
               solver_search_performed=False, unchanged_original_script_parse=False,
               native_bridge_sha256=native_sha, cvc5_sha256=cvc5_sha)
    streams = [{}, {}]
    children, threads = [], []
    def pump(index, source, destination):
        digest, size = hashlib.sha256(), 0
        try:
            with source, destination:
                while block := source.read(1024 * 1024):
                    destination.write(block)
                    digest.update(block)
                    size += len(block)
                destination.flush()
            streams[index].update(complete_eof=True, bytes=size, sha256=digest.hexdigest())
        except BaseException as error:
            streams[index].update(complete_eof=False, bytes=size, sha256=digest.hexdigest(), error=repr(error))
    try:
        with (directory / 'bridge.stderr').open('xb') as native_err, (directory / 'cvc5.stdout').open('xb') as parser_out, (directory / 'cvc5.stderr').open('xb') as parser_err:
            # The guard covers both forks: the current worker leaf becomes two.
            # A controller supplies a shared admission guard for this extra leaf.
            with spawn_guard() if spawn_guard is not None else nullcontext():
                native = subprocess.Popen([str(bridge_executable), '/proc/self/fd/0'],
                                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=native_err)
                children.append(native)
                parser = subprocess.Popen([str(cvc5), '--lang=smt2', '--parse-only'],
                                          stdin=subprocess.PIPE, stdout=parser_out, stderr=parser_err)
                children.append(parser)
            row['whole_module_loading_performed'] = True
            processes = [dict(pid=p.pid, start_ticks=Path(f'/proc/{p.pid}/stat').read_text().rsplit(')', 1)[1].split()[19], argv=p.args) for p in children]
            (directory / 'processes.json').write_text(json.dumps(processes, indent=2) + '\n')
            threads = [threading.Thread(target=pump, args=(0, open_input(target), native.stdin)),
                       threading.Thread(target=pump, args=(1, native.stdout, parser.stdin))]
            for thread in threads:
                thread.start()
            _, status, native_usage = os.wait4(native.pid, 0)
            native.returncode = os.waitstatus_to_exitcode(status)
            for thread in threads:
                thread.join()
            _, status, parser_usage = os.wait4(parser.pid, 0)
            parser.returncode = os.waitstatus_to_exitcode(status)
        receipt = json.loads((directory / 'bridge.stderr').read_text())
        row.update(bridge=receipt, original_stream=streams[0], bridged_stream=streams[1],
                   native_returncode=native.returncode, cvc5_returncode=parser.returncode,
                   native_peak_rss_kib=native_usage.ru_maxrss, cvc5_peak_rss_kib=parser_usage.ru_maxrss)
        row['passed'] = (native.returncode == parser.returncode == 0
                         and receipt.get('status') == 'bridged' and receipt.get('original_eof') is True
                         and all(r.get('complete_eof') is True for r in streams)
                         and sha(bridge_executable) == native_sha and sha(cvc5) == cvc5_sha)
    except BaseException as error:
        row.update(error=repr(error), original_stream=streams[0], bridged_stream=streams[1])
    finally:
        # Only the children created by this invocation are cleaned up on failure.
        for child in children:
            if child.poll() is None:
                child.kill()
                child.wait()
        for thread in threads:
            if thread.is_alive():
                thread.join()
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target')
    parser.add_argument('--bridge-executable', required=True)
    parser.add_argument('--cvc5', required=True)
    parser.add_argument('--work-directory', required=True)
    args = parser.parse_args()
    row = load_whole(args.target, args.bridge_executable, args.cvc5, args.work_directory)
    print(json.dumps(row))
    return 0 if row['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
