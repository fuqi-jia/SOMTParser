"""Independent Z3 parsing and lexical boundary tests for bounded SMT validation."""
import errno
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys

import pytest

pytest.importorskip('z3')
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import validate_packed_smt_stream as validator


PREFIX = '(set-logic ALL)\n(declare-fun x () Int)\n'
TAIL = '\n(check-sat)\n(exit)\n'


def run(tmp_path, text, *, zipped=False, **limits):
    payload = text.encode() if isinstance(text, str) else text
    path = tmp_path / ('input.smt2.gz' if zipped else 'input.smt2')
    path.write_bytes(gzip.compress(payload, mtime=0) if zipped else payload)
    report = validator.Validator(path, tmp_path/'validation', batch_commands=2, **limits).run()
    assert report['whole_module_parse'] is False and report['solver_check'] is False
    assert report['input']['sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
    assert report == json.loads((tmp_path/'validation/report.json').read_text())
    return report


def test_every_batch_replays_closed_declarations_and_definitions(tmp_path):
    source = (PREFIX + '(define-fun bump ((a Int)) Int (+ a 1))\n'
              + '\n'.join(f'(assert (= (bump x) {i}))' for i in range(7))
              + '\n(minimize (bump x))\n(maximize x)'
              + '\n(check-sat)\n(get-objectives)\n(get-model)\n(exit)\n; final comment')
    report = run(tmp_path, source, zipped=True)
    assert report['ok'], report
    assert report['assertions'] == report['parsed_assertions'] == 7
    assert report['objectives'] == report['parsed_objectives'] == 2
    assert report['commands'] == 16 and report['prefix_commands'] == 3
    assert report['batches'] == 6  # Prefix plus five bounded body batches.
    assert report['decoded_input'] == dict(bytes=len(source.encode()), complete=True,
                                           sha256=hashlib.sha256(source.encode()).hexdigest())
    rows = [json.loads(line) for line in (tmp_path/'validation/batches.jsonl').read_text().splitlines()]
    assert all(row['result']['ok'] and row['returncode'] == 0 for row in rows)
    assert sum(row['result']['assertions'] for row in rows) == 7
    assert sum(row['result']['objectives'] for row in rows) == 2
    assert all(row['command_count'] <= 2 for row in rows)


@pytest.mark.parametrize('bad_position', [0, 2, 4])
def test_sort_error_in_first_middle_and_final_batch_identifies_original_command(tmp_path, bad_position):
    assertions = ['(assert (= x 1))'] * 5
    assertions[bad_position] = '(assert (+ x 1))'
    report = run(tmp_path, PREFIX + '\n'.join(assertions) + TAIL)
    assert not report['ok']
    assert report['failed_command']['index'] == 3 + bad_position
    assert report['failed_batch']['result']['error']
    assert (tmp_path/'validation/failure-command.smt2').read_text() == assertions[bad_position]


def test_invalid_final_objective_is_not_omitted(tmp_path):
    report = run(tmp_path, PREFIX + '(assert (> x 0))\n(minimize (+ x absent))' + TAIL)
    assert not report['ok'] and report['failed_command']['index'] == 4


def test_nonclosed_definition_prefix_is_rejected(tmp_path):
    report = run(tmp_path, PREFIX + '(define-fun f () Int later)\n(declare-const later Int)' + TAIL)
    assert not report['ok']
    assert report['failed_batch']['prefix_only']
    assert report['failed_command']['index'] == 3


@pytest.mark.parametrize('source, message', [
    (PREFIX + '(declare-const |x| Int)' + TAIL, 'duplicate declared name'),
    (PREFIX + '(assert true)\n(declare-const y Int)' + TAIL, 'late declaration'),
    (PREFIX + '(assert true)\n(define-fun f () Int 1)' + TAIL, 'late declaration'),
    (PREFIX + '(assert (! true :named n))\n(assert (! false :named n))' + TAIL, ':named'),
    (PREFIX + '(minimize x)\n(assert true)' + TAIL, 'permitted phase'),
    (PREFIX + '(push 1)' + TAIL, 'unsupported command'),
    (PREFIX + '(pop 1)' + TAIL, 'unsupported command'),
    (PREFIX + '(reset)' + TAIL, 'unsupported command'),
    ('(set-option :regular-output-channel "ignored")' + PREFIX + TAIL, 'set-option'),
    ('(set-option :timeout 1)' + PREFIX + TAIL, 'set-option'),
    (PREFIX + '(check-sat)\n(check-sat)\n(exit)', 'repeated command'),
    (PREFIX + '(check-sat 1)\n(exit)', 'no arguments'),
    (PREFIX + '(get-model)\n(check-sat)\n(exit)', 'check-sat first'),
    (PREFIX + '(check-sat)\n(get-value (x))\n(exit)', 'unsupported command'),
    (PREFIX + TAIL + '(assert true)', 'permitted phase'),
    (PREFIX + TAIL + '(exit)', 'after exit'),
    (PREFIX + '(assert true)\n(check-sat)', 'mandatory check-sat/exit'),
])
def test_reject_unsupported_state_or_damaged_query_tail(tmp_path, source, message):
    report = run(tmp_path, source)
    assert not report['ok'] and message in report['error'], report


def test_named_keyword_inside_strings_symbols_comments_is_not_an_attribute(tmp_path):
    source = ('(set-logic ALL)\n(set-option :produce-models true)\n'
              '(set-option :opt.priority lex)\n(declare-const |:named| String)\n'
              '(assert (= |:named| "text :named; ( ) and ""quotes"""))\n'
              '; :named not an attribute\n(assert true)' + TAIL)
    report = run(tmp_path, source)
    assert report['ok'], report
    assert report['parsed_assertions'] == 2


@pytest.mark.parametrize('chunk_bytes', [1, 2, 7, 65536])
def test_lexer_handles_chunk_boundaries_comments_doubled_quotes_and_quoted_symbols(chunk_bytes):
    payload = (b'; leading )\n(declare-const |x(;)| String)\n'
               b'(assert (= |x(;)| "a;(""b)")) ; )\n(check-sat)\n(exit);end')
    rows = list(validator.commands(io.BytesIO(payload), max_command_bytes=1000, chunk_bytes=chunk_bytes))
    assert len(rows) == 4
    assert [validator.command_head(row)[0] for row in rows] == ['declare-const','assert','check-sat','exit']
    assert all(payload[row.start:row.end] == row.raw for row in rows)
    assert [row.line for row in rows] == [2, 3, 4, 5]


@pytest.mark.parametrize('suffix', [')', 'garbage', '(exit', '(assert "open)', '(assert |open)',
                                     '(assert |bad\\name|)'])
def test_malformed_lexical_tail_never_passes(tmp_path, suffix):
    report = run(tmp_path, PREFIX + '(assert true)' + TAIL + suffix)
    assert not report['ok']


def test_truncated_gzip_is_rejected_even_with_a_valid_smt_tail(tmp_path):
    payload = gzip.compress((PREFIX + '(assert true)' + TAIL).encode(), mtime=0)
    path = tmp_path/'truncated.gz'
    path.write_bytes(payload[:-4])
    report = validator.Validator(path, tmp_path/'validation').run()
    assert not report['ok'] and 'EOFError' in report['error']
    assert not report['decoded_input']['complete']


def test_body_byte_limit_and_prefix_byte_limit_are_explicit_failures(tmp_path):
    source = tmp_path/'input.smt2'
    source.write_text(PREFIX + '(assert (> x 123456789))' + TAIL)
    first = validator.Validator(source, tmp_path/'prefix-limit', max_prefix_bytes=10).run()
    assert not first['ok'] and 'prefix byte budget' in first['error']
    second = validator.Validator(source, tmp_path/'body-limit', batch_bytes=12).run()
    assert not second['ok'] and 'batch byte budget' in second['error']


def test_thousand_assertions_all_covered_in_bounded_batches(tmp_path):
    source = PREFIX + '\n'.join(f'(assert (= x {i}))' for i in range(1000)) + TAIL
    path = tmp_path/'input.smt2'; path.write_text(source)
    report = validator.Validator(path, tmp_path/'validation', batch_commands=127).run()
    assert report['ok'], report
    assert report['assertions'] == report['parsed_assertions'] == 1000
    assert report['objectives'] == 0 and report['batches'] == 9


def test_unknown_z3_runtime_pin_is_a_real_failure(tmp_path):
    report = run(tmp_path, PREFIX + '(assert true)' + TAIL, expected_version='not-this-version')
    assert not report['ok']
    assert 'runtime mismatch' in report['failed_batch']['result']['error']


def test_total_cpu_budget_includes_controller_work(tmp_path):
    report = run(tmp_path, PREFIX + '(assert true)' + TAIL, total_cpu_seconds=0.00000001)
    assert not report['ok']
    assert 'total cumulative CPU budget exceeded' in report['error']
    assert report['total_cpu_seconds'] >= report['controller_cpu_seconds']
    assert report['batches'] == 0


@pytest.mark.parametrize('code', [errno.ENOENT, errno.ESRCH, errno.EACCES, errno.EIO])
def test_cpu_observation_only_tolerates_child_disappearance(tmp_path, monkeypatch, code):
    instance = validator.Validator(tmp_path / 'input', tmp_path / 'output')

    def fail(_path):
        raise OSError(code, 'injected procfs read failure')

    monkeypatch.setattr(Path, 'read_text', fail)
    if code in (errno.ENOENT, errno.ESRCH):
        instance._budget(active_pid=123)
        # Losing the live sample must not bypass the already-accounted budget.
        instance.child_cpu = instance.limits['total_cpu_seconds']
        with pytest.raises(validator.Rejected, match='total cumulative CPU budget'):
            instance._budget(active_pid=123)
    else:
        with pytest.raises(OSError) as caught:
            instance._budget(active_pid=123)
        assert caught.value.errno == code


def test_nul_in_final_comment_is_rejected_after_complete_batches(tmp_path):
    source = (PREFIX + '(assert (= x 1))' + TAIL + '; trailing comment\x00').encode()
    report = run(tmp_path, source)
    assert not report['ok'] and 'NUL byte' in report['error'], report
    assert report['byte_offset'] == source.index(b'\x00')
    assert report['parsed_assertions'] == 1


def test_nul_inside_string_is_rejected_before_c_string_parser(tmp_path):
    source = b'(declare-const s String)\n(assert (= s "before\x00after"))' + TAIL.encode()
    report = run(tmp_path, source)
    assert not report['ok'] and 'NUL byte' in report['error'], report
    assert report['byte_offset'] == source.index(b'\x00')
    assert report['failed_command']['index'] == 2
    assert report['parsed_assertions'] == 0
