"""Whole-module WCNF loading against an independent Python bridge.

Every emitted term is compared token-for-token, then parsed by CVC5. Separate
streaming tests require both processes, both complete EOFs, and original hashes.
Source relation and weighted-cost equivalence require the separate certificate.
"""
from pathlib import Path
import gzip
import hashlib
import io
import json
import os
import shutil
import subprocess
import tempfile
import pytest
from tools.semantic_checks.wcnf_load_reference import bridge as reference_bridge
from tools.semantic_checks import wcnf_native_load as module
from tools.validate_packed_smt_stream import HashReader, Rejected, commands, command_head


@pytest.fixture(autouse=True)
def qualified_binaries(monkeypatch):
    repository = Path(__file__).resolve().parents[2]
    explicit = os.environ.get('SOMT_WCNF_LOAD_BRIDGE')
    build = Path(os.environ.get('SOMTPARSER_BUILD_DIR', str(repository / 'build-rel')))
    candidates = [Path(explicit)] if explicit else [build / 'tools/somt-wcnf-load-bridge']
    installed = shutil.which('somt-wcnf-load-bridge')
    if installed:
        candidates.append(Path(installed))
    binary = next((p.resolve() for p in candidates if p.is_file()), None)
    cvc5 = os.environ.get('SOMTPARSER_CVC5') or shutil.which('cvc5')
    if binary is None or not cvc5:
        pytest.skip('build somt-wcnf-load-bridge and provide CVC5 for whole-module loading')
    monkeypatch.setenv('SOMT_WCNF_LOAD_BRIDGE', str(binary))
    monkeypatch.setenv('SOMTPARSER_CVC5', str(cvc5))


def normalized(raw):
    return [(head,list(tokens)) for command in commands(HashReader(io.BytesIO(raw)),max_command_bytes=float('inf')) for head,tokens in [command_head(command)]]

def bridge(source,destination):
    raw=source.read();reference=io.BytesIO()
    try:expected=reference_bridge(io.BytesIO(raw),reference);reference_ok=True
    except Rejected:reference_ok=False
    with tempfile.TemporaryDirectory(prefix='wcnf-bridge-') as directory:
        path=Path(directory)/'original.smt2';path.write_bytes(raw)
        p=subprocess.run([os.environ['SOMT_WCNF_LOAD_BRIDGE'],str(path)],capture_output=True)
    if p.returncode:
        if reference_ok:raise AssertionError('native rejects independent-reference accepted module: '+p.stderr.decode(errors='replace'))
        raise Rejected('both bridge implementations rejected input')
    assert reference_ok,'native accepted independent-reference rejected module'
    receipt=json.loads(p.stderr);assert receipt['status']=='bridged' and receipt['original_eof']
    assert normalized(p.stdout)==normalized(reference.getvalue()),'native changed a term or command token'
    for key in ['commands','declarations','hard_assertions','soft_assertions']:
        assert receipt[key]==expected[key],key
    destination.write(p.stdout)
    receipt.update(original_bytes=len(raw),original_sha256=hashlib.sha256(raw).hexdigest(),bridged_bytes=len(p.stdout),bridged_sha256=hashlib.sha256(p.stdout).hexdigest(),independent_python_output_tokens_equal=True)
    return receipt


PREFIX = b'(set-logic ALL) (declare-const x Bool) '
TAIL = b' (check-sat) (exit)'


def parse(source):
    out = io.BytesIO()
    receipt = bridge(io.BytesIO(source), out)
    result = subprocess.run([os.environ['SOMTPARSER_CVC5'], '--lang=smt2', '--parse-only'],
                            input=out.getvalue(), capture_output=True)
    return receipt, result


@pytest.mark.parametrize('body', [
    b'(assert x) (assert-soft (not x) :weight 9007199254740993)',
    b'(assert-soft false :weight 3) (assert-soft true :weight 5)',
    b'(assert-soft (let ((|somt.soft.check| x)) (not |somt.soft.check|)) :weight 7)',
])
def test_full_soft_boolean_terms_are_typed_without_solving(body):
    receipt, result = parse(PREFIX + body + TAIL)
    assert result.returncode == 0, result.stderr
    assert receipt['original_eof'] and receipt['original_bytes'] == len(PREFIX + body + TAIL)
    assert receipt['soft_assertions'] >= 1
    assert receipt['solver_search'] is False


@pytest.mark.parametrize('body', [
    b'(assert-soft missing :weight 1)',
    b'(assert-soft 1 :weight 1)',
    b'(assert-soft (+ x 1) :weight 1)',
    b'(assert (+ x 1)) (assert-soft x :weight 1)',
])
def test_all_original_terms_are_typechecked(body):
    _, result = parse(PREFIX + body + TAIL)
    assert result.returncode != 0


@pytest.mark.parametrize('body,tail', [
    (b'(assert-soft x :weight 0)', TAIL),
    (b'(assert-soft x :weight -1)', TAIL),
    (b'(assert-soft x :weight 1 :id g)', TAIL),
    (b'(assert-soft x :weight 1 :weight 2)', TAIL),
    (b'(assert-soft x)', TAIL),
    (b'(minimize 1)', TAIL),
    (b'(assert-soft x :weight 1)', TAIL + b' (assert x)'),
    (b'(assert-soft x :weight 1)', b' (exit)'),
    (b'(assert-soft x :weight 1)', b' (check-sat)'),
    (b'(assert-soft (or x) :weight 1', TAIL),
])
def test_unsupported_or_incomplete_commands_cannot_be_dropped(body, tail):
    with pytest.raises(Rejected):
        bridge(io.BytesIO(PREFIX + body + tail), io.BytesIO())


LEXICAL_PREFIX=b'(set-logic ALL)(declare-const x Bool)'
LEXICAL_TAIL=b'(check-sat)(exit)'

def load(source):
    output=io.BytesIO();row=bridge(io.BytesIO(source),output)
    p=subprocess.run([os.environ['SOMTPARSER_CVC5'],'--lang=smt2','--parse-only'],input=output.getvalue(),capture_output=True)
    assert p.returncode==0,p.stderr
    assert row['independent_python_output_tokens_equal'] and row['original_eof']
    return row

@pytest.mark.parametrize('kind',['comments','quoted','strings','large_decimal'])
def test_lexical_read_boundaries_preserve_original_terms(kind):
    if kind=='comments':raw=b';'+b' padding'*10000+b'\n'+LEXICAL_PREFIX+b'(assert-soft (not; comment\nx) :weight 1)'+LEXICAL_TAIL
    elif kind=='quoted':
        name=b'|'+b'p'*66000+b'|';raw=b'(declare-const '+name+b' Bool)(assert-soft (not '+name+b') :weight 12)'+LEXICAL_TAIL
    elif kind=='strings':raw=LEXICAL_PREFIX+b'(assert-soft (= "a""b'+b'c'*66000+b'" "a""b'+b'c'*66000+b'") :weight 1)'+LEXICAL_TAIL
    else:raw=LEXICAL_PREFIX+b'(assert-soft x :weight '+b'9'*10000+b')'+LEXICAL_TAIL
    assert load(raw)['soft_assertions']==1

@pytest.mark.parametrize('where',['prefix','declaration','term','after_exit','comment'])
def test_nul_is_rejected_throughout_complete_input(where):
    pieces={'prefix':b'\x00'+LEXICAL_PREFIX+b'(assert x)'+LEXICAL_TAIL,'declaration':LEXICAL_PREFIX.replace(b' x ',b' x\x00 ')+b'(assert x)'+LEXICAL_TAIL,'term':LEXICAL_PREFIX+b'(assert-soft (not x\x00) :weight 1)'+LEXICAL_TAIL,'after_exit':LEXICAL_PREFIX+b'(assert x)'+LEXICAL_TAIL+b'\x00','comment':LEXICAL_PREFIX+b'(assert x)'+LEXICAL_TAIL+b';ignored\x00'}
    with pytest.raises(Rejected):bridge(io.BytesIO(pieces[where]),io.BytesIO())

@pytest.mark.parametrize('body',[b'(check-sat)(check-sat)(exit)',b'(check-sat x)(exit)',b'(assert x)(declare-const y Bool)(check-sat)(exit)',b'(assert-soft |unterminated :weight 1)(check-sat)(exit)'])
def test_invalid_envelope_or_quoted_token_cannot_be_dropped(body):
    with pytest.raises(Rejected):bridge(io.BytesIO(LEXICAL_PREFIX+body),io.BytesIO())

def test_many_commands_across_buffer_boundaries():
    n=3000;raw=b''.join(f'(declare-const x{i} Bool)'.encode() for i in range(n))+b''.join(f'(assert x{i})(assert-soft (not x{i}) :weight {i+1})'.encode() for i in range(n))+LEXICAL_TAIL
    row=load(raw);assert row['declarations']==row['hard_assertions']==row['soft_assertions']==n

def test_simultaneous_let_preserves_original_shadowed_name_scope():
    raw=b'(declare-const |somt.soft.check| Bool)(assert-soft (not |somt.soft.check|) :weight 1)'+LEXICAL_TAIL
    assert load(raw)['soft_assertions']==1


RAW=b'(set-logic ALL)(declare-const x Bool)(assert (not x))(assert-soft x :weight 123456789123456789)(check-sat)(exit)'
@pytest.mark.parametrize('compressed',[False,True])
def test_entire_original_and_bridged_streams_loaded(tmp_path,compressed):
 p=tmp_path/'target';p.write_bytes(gzip.compress(RAW) if compressed else RAW)
 row=module.load_whole(p,os.environ['SOMT_WCNF_LOAD_BRIDGE'],os.environ['SOMTPARSER_CVC5'],tmp_path/'logs')
 assert row['passed'] and row['whole_module_loading_performed']
 assert not row['source_relation_checked'] and not row['weighted_cost_checked']
 assert row['original_stream']==dict(complete_eof=True,bytes=len(RAW),sha256=hashlib.sha256(RAW).hexdigest())
 assert row['bridged_stream']['complete_eof'] and row['bridged_stream']['bytes']>0
 assert row['bridge']['hard_assertions']==row['bridge']['soft_assertions']==1
 assert row['native_returncode']==row['cvc5_returncode']==0
 assert row['native_bridge_sha256']==module.sha(os.environ['SOMT_WCNF_LOAD_BRIDGE'])
 assert row['cvc5_sha256']==module.sha(os.environ['SOMTPARSER_CVC5'])
@pytest.mark.parametrize('kind',['ill_sorted','post_exit'])
def test_parser_error_or_rejected_tail_cannot_be_a_load_pass(tmp_path,kind):
 raw=RAW.replace(b'(assert (not x))',b'(assert (+ x 1))') if kind=='ill_sorted' else RAW+b'(assert x)'+b' '*1048576
 p=tmp_path/'target';p.write_bytes(gzip.compress(raw))
 row=module.load_whole(p,os.environ['SOMT_WCNF_LOAD_BRIDGE'],os.environ['SOMTPARSER_CVC5'],tmp_path/'logs')
 assert not row['passed']
 if kind=='ill_sorted':assert row['cvc5_returncode']!=0
 else:assert row['native_returncode']!=0


def test_spawn_guard_holds_one_shared_lock_for_both_children(tmp_path, monkeypatch):
    from contextlib import contextmanager
    import fcntl
    lock_path = tmp_path / 'shared-admission.lock'
    forks = []
    real_popen = subprocess.Popen
    @contextmanager
    def guard():
        with lock_path.open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(lock, fcntl.LOCK_UN)
    def checked_popen(*args, **kwargs):
        with lock_path.open('a') as probe:
            with pytest.raises(BlockingIOError):
                fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        forks.append(args[0])
        return real_popen(*args, **kwargs)
    monkeypatch.setattr(module.subprocess, 'Popen', checked_popen)
    target = tmp_path / 'target'; target.write_bytes(RAW)
    row = module.load_whole(target, os.environ['SOMT_WCNF_LOAD_BRIDGE'],
                            os.environ['SOMTPARSER_CVC5'], tmp_path / 'logs',
                            spawn_guard=guard)
    assert row['passed'] and len(forks) == 2
    with lock_path.open('a') as probe:
        fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)


def test_failed_spawn_guard_never_starts_a_partial_load(tmp_path, monkeypatch):
    from contextlib import contextmanager
    @contextmanager
    def unavailable():
        raise RuntimeError('admission unavailable')
        yield
    def unexpected(*args, **kwargs):
        pytest.fail('guard failure must precede either child fork')
    monkeypatch.setattr(module.subprocess, 'Popen', unexpected)
    target = tmp_path / 'target'; target.write_bytes(RAW)
    row = module.load_whole(target, os.environ['SOMT_WCNF_LOAD_BRIDGE'],
                            os.environ['SOMTPARSER_CVC5'], tmp_path / 'logs',
                            spawn_guard=unavailable)
    assert not row['passed'] and not row['whole_module_loading_performed']
    assert 'admission unavailable' in row['error']
