"""Optimize parsing and feeder EOF have distinct validation scopes."""
import gzip
import hashlib
import importlib.util
import io
from pathlib import Path
import sys
import threading
from types import SimpleNamespace

import pytest

z3 = pytest.importorskip('z3')
_path = Path(__file__).resolve().parents[2] / 'tools/semantic_checks/parse_omt_stream.py'
_spec = importlib.util.spec_from_file_location('parse_omt_stream', _path)
parser = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(parser)
_checker_path = _path.with_name('wcnf_stream_equivalence.py')
_checker_spec = importlib.util.spec_from_file_location('omt_test_wcnf_checker', _checker_path)
checker = importlib.util.module_from_spec(_checker_spec)
sys.modules[_checker_spec.name] = checker
_checker_spec.loader.exec_module(checker)

VALID = b'(declare-const x Bool)\n(assert x)\n(assert-soft (not x) :weight 17)\n'
LONG_VALID = VALID + b'(assert (or x (not x)))\n' * 12000


def check_receipt(receipt, data):
    assert receipt['parsed']
    assert receipt['target'] == dict(sha256=hashlib.sha256(data).hexdigest(),
                                     bytes=len(data), source_eof=True)


@pytest.mark.parametrize('inherited, expected', [
    ((512 * 1024 ** 2, -1), 512 * 1024 ** 2),
    ((-1, 1024 ** 3), 1024 ** 3),
    ((-1, -1), 2 * 1024 ** 3),
])
def test_worker_memory_default_never_exceeds_inherited_limits(monkeypatch, inherited, expected):
    class FakeResource:
        RLIMIT_AS = 7
        RLIM_INFINITY = -1

        def __init__(self):
            self.applied = None

        def getrlimit(self, kind):
            assert kind == self.RLIMIT_AS
            return inherited

        def setrlimit(self, kind, limits):
            assert kind == self.RLIMIT_AS
            self.applied = limits

    fake = FakeResource()
    monkeypatch.setattr(parser, 'resource', fake)
    parser.set_worker_memory_limit()
    assert fake.applied == (expected, expected)


def test_complete_optimize_parse_preserves_exact_input_hash(tmp_path):
    path = tmp_path / 'model.smt2'
    path.write_bytes(VALID)
    old = z3.Optimize()
    old.from_file(str(path))
    assert len(old.assertions()) == 1 and len(old.objectives()) == 1
    check_receipt(parser.parse_target(z3, path), VALID)


def test_no_ast_vector_copies_or_feeder_thread(tmp_path, monkeypatch):
    path = tmp_path / 'model.smt2'
    path.write_bytes(VALID)

    class NoAstCopies:
        def __init__(self):
            self.inner = z3.Optimize()

        def from_file(self, name):
            self.inner.from_file(name)

        def assertions(self):
            raise AssertionError('must not copy the assertion vector')

        def objectives(self):
            raise AssertionError('must not materialize the aggregate objective')

    def no_thread(*args, **kwargs):
        raise AssertionError('feeder must not reserve a stack in the parser process')

    monkeypatch.setattr(threading, 'Thread', no_thread)
    proxy = SimpleNamespace(Optimize=NoAstCopies, get_version_string=z3.get_version_string)
    check_receipt(parser.parse_target(proxy, path), VALID)


def test_gzip_stream_crosses_pipe_capacity_and_rejects_truncated_archive(tmp_path):
    path = tmp_path / 'model.smt2.gz'
    compressed = gzip.compress(LONG_VALID)
    path.write_bytes(compressed)
    check_receipt(parser.parse_target(z3, path, compressed=True), LONG_VALID)
    # The SMT text is complete, but the archive's EOF/checksum is missing.
    # A parser-only success must not hide the feeder's failed integrity check.
    path.write_bytes(compressed[:-8])
    # gzip may raise before returning its last partial chunk; either the
    # feeder integrity failure or Z3's resulting incomplete syntax rejects it.
    with pytest.raises((RuntimeError, z3.Z3Exception)):
        parser.parse_target(z3, path, compressed=True)


@pytest.mark.parametrize('suffix', [
    b'(assert unknown_symbol)\n',
    b'(assert (+ 1 2))\n',
    b'(assert (and x)\n',
], ids=['unknown-symbol', 'wrong-sort', 'truncated-syntax'])
def test_z3_checks_pre_exit_syntax_and_certificate_catches_post_exit_content(tmp_path, suffix):
    path = tmp_path / 'model.smt2'
    path.write_bytes(LONG_VALID + b'(check-sat)\n' + suffix)
    with pytest.raises(z3.Z3Exception):
        parser.parse_target(z3, path)

    # Z3 stops at exit: writing every byte into its pipe does not prove that
    # Z3 interpreted those bytes. The independent whole-input checker covers it.
    source = b'p wcnf 1 1 2\n1 1 0\n'
    target = (b'(declare-const x1 Bool)\n(assert-soft (or x1) :weight 1)\n'
              b'(check-sat)\n(exit)\n' + suffix)
    path.write_bytes(target)
    native = z3.Optimize()
    native.from_file(str(path))
    receipt = parser.parse_target(z3, path)
    check_receipt(receipt, target)
    assert receipt['parser_stop_policy'] == 'first exit or EOF'
    assert receipt['hash_scope'] == 'all bytes fed'
    assert receipt['complete_target_validation'] == 'requires matching structural certificate including EOF'
    assert checker.verify_streams(io.BytesIO(source), io.BytesIO(target[:-len(suffix)]))['status'] == 'verified'
    with pytest.raises(checker.VerificationError):
        checker.verify_streams(io.BytesIO(source), io.BytesIO(target))


def test_early_reader_close_reaps_feeder_and_never_accepts_partial_input(tmp_path, capfd):
    path = tmp_path / 'model.smt2'
    path.write_bytes(LONG_VALID)

    class EarlyReader:
        def from_file(self, name):
            return

    proxy = SimpleNamespace(Optimize=EarlyReader, get_version_string=z3.get_version_string)
    with pytest.raises(RuntimeError, match='input feeder failed'):
        parser.parse_target(proxy, path)
    assert capfd.readouterr().err == ''


def test_native_abrupt_exit_cannot_append_to_finalized_parser_log(tmp_path):
    import os
    import subprocess
    import time

    fifo = tmp_path / 'source.fifo'
    os.mkfifo(fifo)
    marker = tmp_path / 'feeder-pid'
    log = tmp_path / 'parser.log'
    script = tmp_path / 'native_exit.py'
    script.write_text("""import importlib.util, os, sys
from pathlib import Path
from types import SimpleNamespace
spec = importlib.util.spec_from_file_location('parser', sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
original_popen = module.subprocess.Popen

def record_feeder(*args, **kwargs):
    process = original_popen(*args, **kwargs)
    Path(sys.argv[3]).write_text(str(process.pid))
    return process

module.subprocess.Popen = record_feeder

class NativeExit:
    def from_file(self, name):
        os._exit(101)  # A native failure cannot execute parse_target's finally.

module.parse_target(SimpleNamespace(Optimize=NativeExit), sys.argv[2])
""")
    with log.open('wb') as output:
        process = subprocess.run([sys.executable, '-B', str(script), str(_path),
                                  str(fifo), str(marker)], stdout=output,
                                 stderr=subprocess.STDOUT,
                                 env=dict(os.environ, TMPDIR=str(tmp_path)), timeout=15)
    assert process.returncode == 101
    initial_hash = hashlib.sha256(log.read_bytes()).hexdigest()
    feeder_pid = int(marker.read_text())
    # Delay the feeder until after its parser has exited and the log was hashed.
    deadline = time.monotonic() + 10
    while True:
        try:
            writer = os.open(fifo, os.O_WRONLY | os.O_NONBLOCK)
            break
        except OSError:
            if time.monotonic() >= deadline:
                raise AssertionError('input feeder did not open its source')
            time.sleep(0.02)
    try:
        os.write(writer, b'(assert true)\n')
    finally:
        os.close(writer)
    while time.monotonic() < deadline:
        status = Path(f'/proc/{feeder_pid}/stat')
        if not status.exists() or status.read_text().split(') ', 1)[1][0] == 'Z':
            break
        time.sleep(0.02)
    else:
        raise AssertionError('orphaned feeder did not exit after its reader closed')
    assert hashlib.sha256(log.read_bytes()).hexdigest() == initial_hash
