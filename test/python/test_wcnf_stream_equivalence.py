"""The independent certificate checker must reject incomplete/wrong exports."""
import hashlib
import importlib.util
import io
from pathlib import Path
import sys

import pytest


_path = Path(__file__).resolve().parents[2] / 'tools/semantic_checks/wcnf_stream_equivalence.py'
_spec = importlib.util.spec_from_file_location('wcnf_stream_equivalence', _path)
checker = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = checker
_spec.loader.exec_module(checker)


SOURCE = b'''c mixed hard/soft, empty clauses, unused header variables
p wcnf 3 4 9007199254740994
9007199254740994 1 -2 0
9007199254740993 2 0
h -1 0
2 0
'''
TARGET = b'''(declare-const x1 Bool)
(declare-const x2 Bool)
(declare-const x3 Bool)
(assert (or x1 (not x2)))
(assert-soft (or x2) :weight 9007199254740993)
(assert (or (not x1)))
(assert-soft false :weight 2)
(check-sat)
(exit)
'''


def verify(source=SOURCE, target=TARGET):
    return checker.verify_streams(io.BytesIO(source), io.BytesIO(target))


def test_complete_correspondence_counts_and_exact_input_hashes():
    result = verify()
    assert result['status'] == 'verified'
    assert result['variables'] == 3
    assert result['clauses'] == 4
    assert result['hard_clauses'] == result['soft_clauses'] == 2
    assert result['literals'] == 4
    assert result['source_sha256'] == hashlib.sha256(SOURCE).hexdigest()
    assert result['target_sha256'] == hashlib.sha256(TARGET).hexdigest()
    assert result['target_solver_parse'] == result['target_solve'] == 'not-run'


def test_target_batch_lexer_preserves_token_boundaries_comments_and_raw_digest():
    raw = b'; preface\n(assert\t(or\x0cx1)); trailing comment\r\n(exit)\n'
    tokens = checker.TargetTokens(io.BytesIO(raw))
    observed = []
    while True:
        token = tokens.take()
        if token is None:
            break
        observed.append(token)
    assert observed == [b'(', b'assert', b'(', b'or', b'x1', b')', b')',
                        b'(', b'exit', b')']
    assert tokens.digest.hexdigest() == hashlib.sha256(raw).hexdigest()


def test_large_single_line_negative_clause_with_comment_at_eof():
    count = 4096
    source = (f'p cnf {count} 1\n'.encode()
              + b''.join(f'-{i} '.encode() for i in range(1, count + 1))
              + b'0\n')
    declarations = b''.join(
        f'(declare-const x{i} Bool)\n'.encode() for i in range(1, count + 1))
    literals = b' '.join(f'(not x{i})'.encode() for i in range(1, count + 1))
    target = declarations + b'(assert-soft (or ' + literals + b') :weight 1) ; EOF comment'
    result = verify(source, target)
    assert result['variables'] == count
    assert result['clauses'] == 1
    assert result['literals'] == count
    assert result['target_sha256'] == hashlib.sha256(target).hexdigest()


@pytest.mark.parametrize('target', [
    TARGET.replace(b'(not x2)', b'x2'),                  # wrong polarity
    TARGET.replace(b'9007199254740993)', b'9007199254740992)'),  # rounded weight
    TARGET.replace(b'(assert (or (not x1)))', b'(assert-soft (or (not x1)) :weight 1)'),
    TARGET.replace(b'(assert-soft false :weight 2)\n', b''),    # dropped empty soft clause
    TARGET.replace(b'false', b'(or)'),                  # invalid zero-argument application
    TARGET.replace(b'false', b'true'),                  # an empty clause is false
    TARGET.replace(b'(or x2)', b'false'),               # nonempty clause erased
    TARGET.replace(b'(declare-const x3 Bool)\n', b''),          # dropped unused source variable
    TARGET.replace(b'(declare-const x2 Bool)', b'(declare-const x1 Bool)'),
    TARGET.replace(b'(or x2)', b'(or x4)'),              # undeclared reference
    TARGET.replace(b'(check-sat)', b'(assert (or x1))'), # inserted constraint
    TARGET.replace(b':weight 2)', b':weight 2 :id another)'),   # changed objective group
    TARGET + b'(assert (or x1))\n',                     # content after exit
    TARGET.replace(b'(exit)', b'(minimize x1)'),        # unsupported extra objective
    TARGET[:TARGET.index(b':weight 2') + len(b':weight')],     # truncated weight
    TARGET[:-3],                                       # truncated final command
])
def test_corrupt_or_incomplete_target_never_verifies(target):
    with pytest.raises(checker.VerificationError):
        verify(target=target)


@pytest.mark.parametrize('source', [
    SOURCE.replace(b'p wcnf 3 4', b'p wcnf 3 5'),
    SOURCE.replace(b'p wcnf 3 4', b'p wcnf 1 4'),
    SOURCE.replace(b'2 0\n', b'0 0\n'),
    SOURCE + b'1 1 0\n',
    SOURCE.replace(b'h -1 0', b'h -1 0 2'),
])
def test_invalid_or_incomplete_source_never_verifies(source):
    with pytest.raises(checker.VerificationError):
        verify(source=source)


def test_headerless_arbitrary_precision_soft_weights_and_comments():
    # More digits than Python's default int-string conversion limit; no float
    # or machine-sized integer may silently alter source/target weights.
    weight = b'7' * 5000
    source = b'c{}\n000' + weight + b' 1 0\nh 0\n'
    target = (b'; preface\n(declare-const x1 Bool)\n(assert-soft\n(or x1)\n:weight '
              + weight + b')\n(assert false) ; empty hard clause\n(check-sat)\n')
    result = verify(source, target)
    assert result['hard_clauses'] == result['soft_clauses'] == 1
    assert result['pointwise_violation_cost_equal']


def test_unweighted_and_empty_header_models():
    assert verify(b'p cnf 1 1\n-1 0\n',
                  b'(declare-const x1 Bool)(assert-soft (or (not x1)) :weight 1)')['clauses'] == 1
    assert verify(b'p wcnf 0 0 10\n', b'(check-sat)(exit)')['variables'] == 0
    with pytest.raises(checker.VerificationError):
        verify(b'', b'')


def test_top_classification_changes_feasibility_not_soft_cost():
    # Numeric >= top is hard even when the clause's weight is far above top.
    source = b'p wcnf 1 1 10\n9007199254740993 1 0\n'
    hard = b'(declare-const x1 Bool)(assert (or x1))'
    assert verify(source, hard)['hard_clauses'] == 1
    with pytest.raises(checker.VerificationError):
        verify(source, b'(declare-const x1 Bool)(assert-soft (or x1) :weight 9007199254740993)')


@pytest.mark.parametrize("byte", range(256))
def test_decimal_validation_accepts_only_ascii_digits(byte):
    token = bytes([byte])
    if 48 <= byte <= 57:
        assert checker._natural(token) == token
    else:
        for invalid in (token, b"1" + token, token + b"2"):
            with pytest.raises(checker.VerificationError):
                checker._natural(invalid)


@pytest.mark.parametrize("number", [0, 1, 10**18, 2**63 - 1])
def test_source_indices_keep_zero_padding_and_exact_64_bit_boundary(number):
    assert checker._index(b"000" + str(number).encode()) == number
    if number:
        assert checker._target_variable(b"x" + str(number).encode()) == number
        with pytest.raises(checker.VerificationError):
            checker._target_variable(b"x0" + str(number).encode())


@pytest.mark.parametrize("token", [b"", b"0", b"00", b"01", b"+1", b"-1", b"1_0",
                                  b"1.0", b"1e1", b"9223372036854775808", b"1" * 5000])
def test_noncanonical_or_out_of_range_target_indices_never_verify(token):
    with pytest.raises(checker.VerificationError):
        checker._target_variable(b"x" + token)


@pytest.mark.parametrize("token", [b"x0", b"x00", b"x01", b"x\xff",
                                    b"x9223372036854775808"])
def test_cached_index_validation_does_not_accept_noncanonical_or_invalid_target_names(token):
    # Prime with the same zero-padded token a source accepts; target spelling must still reject x01.
    assert checker._positive_index(b"01") == 1
    with pytest.raises(checker.VerificationError):
        checker._target_variable(token)


def test_long_zero_padded_source_index_remains_valid_without_retaining_large_cache_key():
    before = checker._cached_positive_index.cache_info().currsize
    assert checker._positive_index(b"0" * 10000 + b"1") == 1
    assert checker._cached_positive_index.cache_info().currsize == before


def test_repeated_opposite_sign_literals_keep_their_weighted_clause_correspondence():
    source = b"p cnf 1 4\n1 0\n-1 0\n1 0\n-1 0\n"
    target = (b"(declare-const x1 Bool)\n(assert-soft (or x1) :weight 1)\n"
              b"(assert-soft (or (not x1)) :weight 1)\n"
              b"(assert-soft (or x1) :weight 1)\n"
              b"(assert-soft (or (not x1)) :weight 1)\n")
    assert checker.verify_streams(io.BytesIO(source), io.BytesIO(target))["clauses"] == 4
    wrong_polarity = target.replace(b"(assert-soft (or (not x1)) :weight 1)",
                                    b"(assert-soft (or x1) :weight 1)", 1)
    with pytest.raises(checker.VerificationError):
        checker.verify_streams(io.BytesIO(source), io.BytesIO(wrong_polarity))
