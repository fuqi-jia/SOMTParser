"""Exact native WCNF certificates against an independent Python implementation.

The Python implementation uses Python sets/counters and its own parser; it does
not call the native checker. Native decoding, full-key equality, soft occurrence
counts, AMO expansion, and complete compressed-stream binding are tested here.
"""
from pathlib import Path
import gzip
import hashlib
import io
import itertools
import json
import lzma
import os
import random
import shutil
import subprocess
import tempfile
import pytest
import z3
from tools.semantic_checks import wcnf_compiled as module
from tools.semantic_checks.wcnf_complete import verify_streams as python_verify
from tools.semantic_checks.wcnf_stream_equivalence import VerificationError


@pytest.fixture(autouse=True)
def native_certificate_binary(monkeypatch):
    repository = Path(__file__).resolve().parents[2]
    explicit = os.environ.get('SOMT_WCNF_CERTIFICATE')
    build = Path(os.environ.get('SOMTPARSER_BUILD_DIR', str(repository / 'build-rel')))
    candidates = [Path(explicit)] if explicit else [build / 'tools/somt-wcnf-certificate']
    installed = shutil.which('somt-wcnf-certificate')
    if installed:
        candidates.append(Path(installed))
    binary = next((p.resolve() for p in candidates if p.is_file()), None)
    if binary is None:
        pytest.skip('build somt-wcnf-certificate or set SOMT_WCNF_CERTIFICATE')
    monkeypatch.setenv('SOMT_WCNF_CERTIFICATE', str(binary))


def cpp_verify(source, target):
    with tempfile.TemporaryDirectory(prefix='wcnf-certificate-') as directory:
        root=Path(directory);(root/'source').write_bytes(source);(root/'target').write_bytes(target)
        p=subprocess.run([os.environ['SOMT_WCNF_CERTIFICATE'],str(root/'source'),str(root/'target')],capture_output=True)
        if p.returncode:
            raise VerificationError(p.stdout.decode(errors='replace')[:500]+p.stderr.decode(errors='replace')[:500])
        row=json.loads(p.stdout)
        if row['status']!='verified':raise VerificationError('native did not verify')
        return row


def verify_streams(source, target):
    source,target=source.read(),target.read()
    try:reference=python_verify(io.BytesIO(source),io.BytesIO(target));python_ok=True
    except VerificationError:python_ok=False
    try:native=cpp_verify(source,target);cpp_ok=True
    except VerificationError:cpp_ok=False
    # Some invalid SMT shapes accepted by the old restricted checker are
    # rejected more strictly by the native certificate, never vice versa.
    if not python_ok and cpp_ok:raise AssertionError('native accepted a Python-rejected relation')
    if python_ok and not cpp_ok:raise AssertionError('native rejected a Python-verified relation')
    if not cpp_ok:raise VerificationError('both independent checkers rejected')
    for key in ['variables','source_clauses','source_hard','source_soft','unique_hard_clauses',
                'soft_clause_occurrences','target_assertions']:
        assert native[key]==reference[key],(key,native[key],reference[key])
    native.update(source_sha256=hashlib.sha256(source).hexdigest(),target_sha256=hashlib.sha256(target).hexdigest(),independent_python_agreed=True)
    return native


SRC=b'p wcnf 3 5 10\nh 1 -2 0\nh -2 1 1 0\n3 2 0\n3 2 0\n2 -3 0\n'
DECL=b'(set-logic ALL)(declare-fun x1 () Bool)(declare-fun x2 () Bool)(declare-fun x3 () Bool)'
SMT=DECL+b'(assert (or (not x2) x1))(assert-soft x2 :weight 3)(assert-soft (not x3) :weight 2)(assert-soft (or x2 x2) :weight 3)(check-sat)(exit)'
def verify(source=SRC,target=SMT):return verify_streams(io.BytesIO(source),io.BytesIO(target))
def test_complete_reordering_duplicates_exact_soft_multiplicity():
    assert verify()['pointwise_violation_cost_equal']
@pytest.mark.parametrize('old,new',[(b':weight 3',b':weight 4'),(b'(not x2)',b'x2'),(b':weight 2',b':weight 1'),(b'(assert-soft x2 :weight 3)',b''),(b'x3 () Bool',b'x3 () Int'),(b'(exit)',b'(exit)(assert true)'),(b'(check-sat)',b'(minimize 0)(check-sat)'),(b':weight 2)',b':weight 2 :id other)'),(b'(set-logic ALL)',b'(set-logic QF_LIA)'),(b'x2 () Bool',b'x2 (Bool) Bool')])
def test_changed_relation_cost_domain_envelope_refused(old,new):
    with pytest.raises(VerificationError):verify(target=SMT.replace(old,new,1))
@pytest.mark.parametrize('signs',[(1,2,3),(-1,2,-3),(1,-1,2),(1,1,2)])
def test_full_amo_truth_table_and_source_pairs(signs):
    source=b'p wcnf 3 3 10\n'+b''.join(('h %s %s 0\n'%(-a,-b)).encode() for a,b in itertools.combinations(signs,2))
    names={i:z3.Bool('x'+str(i)) for i in range(1,4)}
    def text(v):return ('x%d'%v if v>0 else '(not x%d)'%-v).encode()
    formula=b'(<= (+ '+b' '.join(b'(ite '+text(v)+b' 1 0)' for v in signs)+b') 1)'
    target=DECL+b'(assert '+formula+b')(check-sat)(exit)'
    assert verify(source,target)['feasibility_equivalent']
    parsed=z3.parse_smt2_string(target.decode())[0]
    for bits in itertools.product([False,True],repeat=3):
        expected=all(not ((bits[abs(a)-1]==(a>0)) and (bits[abs(b)-1]==(b>0))) for a,b in itertools.combinations(signs,2))
        actual=z3.simplify(z3.substitute(parsed,*[(names[i],z3.BoolVal(bits[i-1])) for i in names]))
        assert z3.is_true(actual)==expected
@pytest.mark.parametrize('bad',[b'(<= (+ (ite x1 1 0) (ite x2 1 0)) 2)',b'(<= (+ (ite x1 2 0) (ite x2 1 0)) 1)',b'(<= (+ (ite x1 1 1) (ite x2 1 0)) 1)'])
def test_non_amo_not_reinterpreted(bad):
    with pytest.raises(VerificationError):verify(b'p wcnf 3 1 10\nh -1 -2 0\n',DECL+b'(assert '+bad+b')(check-sat)(exit)')
def test_empty_and_tautological_soft_clauses_preserve_constant_cost():
    s=b'p wcnf 1 3 10\nh 1 -1 0\n3 1 -1 0\n2 0\n'
    t=b'(declare-const x1 Bool)(assert-soft false :weight 2)(check-sat)(exit)'
    assert verify(s,t)['pointwise_violation_cost_equal']
    with pytest.raises(VerificationError):verify(s,t.replace(b'false',b'true'))
def test_arbitrary_precision_weight_bytes():
    w=b'7'*5000
    assert verify(b'p wcnf 1 1\n'+w+b' 1 0\n',b'(declare-const x1 Bool)(assert-soft x1 :weight '+w+b')')['pointwise_violation_cost_equal']
@pytest.mark.parametrize('source',[SRC,b'p wcnf 5 11 10\n'+b''.join(('h -%d -%d 0\n'%(a,b)).encode() for a,b in itertools.combinations(range(1,6),2))+b'3 1 2 0\n'])
def test_real_native_expanded_export_full_correspondence(source):
    import somtparser as sp
    result=sp.translate(source=source.decode(),language='wcnf',dialect=sp.OmtDialect.Z3)
    assert result.ok,[d.message for d in result.diagnostic_items]
    assert verify(source,result.to_smt2(dialect=sp.OmtDialect.Z3).encode())['pointwise_violation_cost_equal']


def check(s,t):return verify_streams(io.BytesIO(s),io.BytesIO(t))
def decl(n):return b''.join(f'(declare-const x{i} Bool)'.encode() for i in range(1,n+1))
def lit(v):return f'x{v}'.encode() if v>0 else f'(not x{-v})'.encode()
def clause(v):return b'(or '+b' '.join(map(lit,v))+b')' if v else b'false'
@pytest.mark.parametrize('replacement',[b'4',b'0',b'-3',b'3.0',b'3 :id g',b'3 :weight 3'])
def test_exact_soft_weight_mutations(replacement):
    s=b'p wcnf 1 1\n3 1 0\n';t=decl(1)+b'(assert-soft x1 :weight '+replacement+b')'
    with pytest.raises(VerificationError):cpp_verify(s,t)
@pytest.mark.parametrize('target',[b'(assert x1)',b'(assert (not x1))',b'(assert (and x1 x1))',b'(assert (or x1 x1))'])
def test_hard_duplicate_idempotence_and_polarity(target):
    s=b'p wcnf 1 2 10\nh 1 0\nh 1 0\n'
    if b'not' in target:
        with pytest.raises(VerificationError):check(s,decl(1)+target)
    else:assert check(s,decl(1)+target)['feasibility_equivalent']
def test_exact_10000_digit_weight_and_last_digit_mutation():
    weight=b'9'*10000;s=b'p wcnf 1 1\n'+weight+b' -1 0\n'
    target=decl(1)+b'(assert-soft (not x1) :weight '+weight+b')'
    assert check(s,target)['pointwise_violation_cost_equal']
    with pytest.raises(VerificationError):cpp_verify(s,target[:-2]+b'8)')
@pytest.mark.parametrize('tail',[b'(assert true)',b'(check-sat)',b'garbage',b'\x00',b'; comment\x00'])
def test_entire_tail_rejected(tail):
    with pytest.raises(VerificationError):cpp_verify(b'p wcnf 0 0\n',b'(check-sat)(exit)'+tail)
@pytest.mark.parametrize('target',[b'(assert (or))',b'(assert (and))',b'(assert (<= (+) 1))',b'(assert (not))',b'(assert (or x1)) junk'])
def test_malformed_relation_never_accepted(target):
    with pytest.raises(VerificationError):cpp_verify(b'p wcnf 1 0 10\n',decl(1)+target)
def test_deep_nested_disjunction_and_conjunction_without_recursion_bound():
    depth=5000;s=b'p wcnf 1 1 10\nh 1 0\n'
    target=decl(1)+b'(assert '+b'(and '*depth+b'(or '*depth+b'x1'+b')'*(2*depth)+b')'
    assert cpp_verify(s,target)['feasibility_equivalent']
@pytest.mark.parametrize('seed',range(24))
def test_all_clauses_soft_multiplicities_and_order(seed):
    rng=random.Random(seed);n=5;rows=[]
    for i in range(30):
        values=[rng.choice([-1,1])*rng.randint(1,n) for _ in range(rng.randrange(5))]
        rows.append((None if rng.randrange(3)==0 else str(rng.randint(1,100000)).encode(),values))
    source=f'p wcnf {n} {len(rows)}\n'.encode()+b''.join((w or b'h')+b' '+b' '.join(str(v).encode() for v in vals)+b' 0\n' for w,vals in rows)
    shuffled=list(rows);rng.shuffle(shuffled)
    target=decl(n)+b''.join(b'(assert '+clause(v)+b')' if w is None else b'(assert-soft '+clause(v)+b' :weight '+w+b')' for w,v in shuffled)+b'(check-sat)(exit)'
    assert check(source,target)['pointwise_violation_cost_equal']
    # Removing a non-tautological soft occurrence changes pointwise cost.
    selected=next(((w,v) for w,v in shuffled if w is not None and all(-x not in v for x in v)),None)
    if selected:
        w,v=selected;needle=b'(assert-soft '+clause(v)+b' :weight '+w+b')'
        with pytest.raises(VerificationError):check(source,target.replace(needle,b'',1))


SOURCE=b'p wcnf 2 3 100\nh 1 -2 0\n17 -1 0\n17 -1 0\n'
TARGET=b'(declare-const x1 Bool)(declare-const x2 Bool)(assert (or x1 (not x2)))(assert-soft (not x1) :weight 17)(assert-soft (not x1) :weight 17)(check-sat)(exit)'
@pytest.mark.parametrize('compressed',[False,True])
def test_full_stream_hashes_and_eof(tmp_path,compressed):
 s=tmp_path/'source';t=tmp_path/'target'
 s.write_bytes(lzma.compress(SOURCE) if compressed else SOURCE);t.write_bytes(gzip.compress(TARGET) if compressed else TARGET)
 row=module.verify_files(s,t,os.environ['SOMT_WCNF_CERTIFICATE'])
 assert row['passed'] and not row['whole_module_loading_performed']
 assert row['source_stream']==dict(sha256=hashlib.sha256(SOURCE).hexdigest(),bytes=len(SOURCE),complete_eof=True)
 assert row['target_stream']==dict(sha256=hashlib.sha256(TARGET).hexdigest(),bytes=len(TARGET),complete_eof=True)
 assert row['native_sha256']==module.sha(os.environ['SOMT_WCNF_CERTIFICATE'])
@pytest.mark.parametrize('corrupt',['source','target'])
def test_stream_rejection_and_early_pipe_close_are_not_passes(tmp_path,corrupt):
 s=tmp_path/'source';t=tmp_path/'target'
 s.write_bytes(SOURCE if corrupt=='target' else b'p wcnf 2 4 100\nh 1 0\n')
 t.write_bytes(TARGET.replace(b':weight 17',b':weight 18',1) if corrupt=='target' else TARGET+b' '*1000000)
 row=module.verify_files(s,t,os.environ['SOMT_WCNF_CERTIFICATE'])
 assert not row['passed'] and row['returncode']!=0
