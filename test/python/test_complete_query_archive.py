"""Complete streaming query archives retain byte identity and solver semantics."""
import gzip
import hashlib
import json
from pathlib import Path
import pytest
import z3
from tools.semantic_checks.query_archive import archive_complete_query


class TextSolver:
    def __init__(self, text):
        self.text = text
        self.calls = 0

    def to_smt2(self):
        self.calls += 1
        return self.text


def verify_archive(path, binding, expected):
    packed = path.read_bytes()
    raw = gzip.decompress(packed)
    assert raw == expected.encode('utf-8')
    assert len(raw) == binding['raw_bytes']
    assert len(packed) == binding['archive_bytes']
    assert hashlib.sha256(raw).hexdigest() == binding['raw_sha256']
    assert hashlib.sha256(packed).hexdigest() == binding['archive_sha256']
    assert binding['archive_profile']['compresslevel'] == 9
    assert not path.with_name(path.name + '.partial').exists()
    return raw


@pytest.mark.parametrize('chunk', [1, 2, 3, 7, 31, 262144])
@pytest.mark.parametrize('text', ['', '; 自然语言→SMT 🌍 é\n(assert true)\n(check-sat)\n',
    '; ' + '边界🙂éα' * 71 + '\n(assert false)\n(check-sat)\n'])
def test_all_utf8_bytes_across_chunk_boundaries(tmp_path, chunk, text):
    solver = TextSolver(text)
    path = tmp_path/'query.smt2.gz'
    events = []
    binding = archive_complete_query(solver, path, chunk_chars=chunk,
                                     progress_callback=events.append)
    verify_archive(path, binding, text)
    assert solver.calls == 1
    names = ['complete-query-to-smt2', 'complete-query-utf8-gzip-write',
             'complete-query-write-finalize', 'complete-query-publish']
    assert [(event['phase'], event['event']) for event in events] == [
        (name, state) for name in names for state in ('started', 'completed')]


def test_quantifiers_and_complete_recursive_definition_replay(tmp_path):
    context = z3.Context()
    integer = z3.IntSort(ctx=context)
    n = z3.Int('递归变量🙂', ctx=context)
    count = z3.RecFunction('完整计数', integer, integer)
    z3.RecAddDefinition(count, n, z3.If(n <= 0, 0, count(n - 1) + 1))
    solver = z3.Solver(ctx=context)
    solver.add(z3.Exists([n], n == 3), count(3) != 3)
    expected = solver.to_smt2()
    assert 'define-funs-rec' in expected and 'exists' in expected
    path = tmp_path/'query.smt2.gz'
    binding = archive_complete_query(solver, path, chunk_chars=5)
    raw = verify_archive(path, binding, expected)
    replay = z3.Solver(ctx=z3.Context())
    replay.from_string(raw.decode())
    assert replay.check() == z3.unsat


@pytest.mark.parametrize('swap', [False, True])
def test_ordered_signed_cost_query_replay_and_counterexample(tmp_path, swap):
    x, first, second = z3.Ints('decision first_cost second_cost')
    source = z3.And(x >= 0, x <= 3, first == x + 1, second == -2 * x)
    target = (z3.And(x >= 0, x <= 3, first == -2*x, second == x+1)
              if swap else source)
    solver = z3.Solver(); solver.add(z3.Xor(source, target))
    expected = solver.to_smt2()
    path = tmp_path/'query.smt2.gz'
    binding = archive_complete_query(solver, path, chunk_chars=11)
    raw = verify_archive(path, binding, expected)
    replay = z3.Solver(ctx=z3.Context()); replay.from_string(raw.decode())
    assert replay.check() == (z3.sat if swap else z3.unsat)


@pytest.mark.parametrize('chunk', [0, -1, True, 1.5, '1'])
def test_invalid_chunk_size_never_truncates_query(tmp_path, chunk):
    path = tmp_path/'query.smt2.gz'
    with pytest.raises(ValueError):
        archive_complete_query(TextSolver('(assert true)'), path, chunk_chars=chunk)
    assert not path.exists()


def test_original_archive_cannot_be_overwritten(tmp_path):
    path = tmp_path/'query.smt2.gz'; path.write_bytes(b'original evidence')
    with pytest.raises(FileExistsError):
        archive_complete_query(TextSolver('(assert true)'), path)
    assert path.read_bytes() == b'original evidence'


def test_existing_partial_is_preserved_before_serializing_again(tmp_path):
    path = tmp_path/'query.smt2.gz'
    partial = path.with_name(path.name + '.partial'); partial.write_bytes(b'failure evidence')
    solver = TextSolver('(assert true)')
    with pytest.raises(FileExistsError):
        archive_complete_query(solver, path)
    assert solver.calls == 0 and partial.read_bytes() == b'failure evidence'
    assert not path.exists()


def test_concurrent_complete_archive_is_not_overwritten(tmp_path):
    path = tmp_path/'query.smt2.gz'
    original = '(assert false)\n(check-sat)\n'
    def progress(event):
        if event['phase'] == 'complete-query-write-finalize' and event['event'] == 'completed':
            path.write_bytes(b'independently published evidence')
    with pytest.raises(FileExistsError):
        archive_complete_query(TextSolver(original), path, progress_callback=progress)
    assert path.read_bytes() == b'independently published evidence'
    assert gzip.decompress(path.with_name(path.name + '.partial').read_bytes()) == original.encode()


def test_short_file_write_is_not_published_as_complete(tmp_path, monkeypatch):
    from tools.semantic_checks import query_archive
    original = query_archive._ArchiveWriter
    class ShortWrite:
        def __init__(self, stream):
            self.stream = stream
            self.shortened = False
        def write(self, data):
            if len(data) > 8 and not self.shortened:
                self.shortened = True
                return self.stream.write(data[:1])
            return self.stream.write(data)
        def flush(self):
            self.stream.flush()
    monkeypatch.setattr(query_archive, '_ArchiveWriter', lambda stream: original(ShortWrite(stream)))
    path = tmp_path/'query.smt2.gz'; events = []
    with pytest.raises(OSError, match='incomplete compressed query write'):
        archive_complete_query(TextSolver('(assert true)'), path, progress_callback=events.append)
    assert not path.exists() and path.with_name(path.name + '.partial').is_file()
    assert events[-1]['event'] == 'failed'


def test_invalid_utf8_preserves_partial_and_never_publishes(tmp_path):
    path = tmp_path/'query.smt2.gz'
    events = []
    with pytest.raises(UnicodeEncodeError):
        archive_complete_query(TextSolver('; prefix\n\ud800'), path,
                               chunk_chars=2, progress_callback=events.append)
    assert not path.exists()
    assert path.with_name(path.name + '.partial').is_file()
    assert events[-1]['phase'] == 'complete-query-utf8-gzip-write'
    assert events[-1]['event'] == 'failed'


