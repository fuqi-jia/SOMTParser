"""Complete-envelope bulk path agrees with the general lexical auditor."""
from collections import Counter
import gzip
import hashlib
import io
from pathlib import Path
import random
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import validate_packed_smt_stream as validator


def reference(data, chunk_bytes):
    reader = validator.HashReader(io.BytesIO(data)); heads = Counter(); exited = False
    for command in validator.commands(reader, max_command_bytes=float('inf'), chunk_bytes=chunk_bytes):
        if exited: raise validator.Rejected('non-comment content after exit')
        head, _ = validator.command_head(command); heads[head] += 1; exited = head == 'exit'
    assert reader.complete
    return {'complete_eof': True, 'sha256': reader.hash.hexdigest(), 'bytes': reader.bytes, 'commands': dict(heads)}


@pytest.mark.parametrize('chunk', [1, 2, 7, 31, 1024, 65536])
@pytest.mark.parametrize('payload', [
    b'', b' \r\n\t', b'(declare-const x Bool)\n(assert (or x (not x)))\n(check-sat)\n(exit)\n',
    b'(assert (assert true))\n(assert true)\n',
    b'; comment\x0d(declare-const |x(;)| String)\n(assert (= |x(;)| "a;(""b)"))\n(exit);tail',
    b'(declare-const x Int)\n(assert\n (= x 3))\n(exit)\n',
    b'(declare-const x Int)\n(assert (= x 3))(check-sat)(exit)',
    b'( ;head comment\nassert true)\n(exit)\n',
    b'(assert true)\n; comment without exit',
    b'(unknown-head (a (b (c (d (e))))))\n',
    b'(assert |non-ascii-\xc3\xa9|)\n',
])
def test_bulk_and_general_auditor_exact_fields(payload, chunk):
    assert validator.complete_envelope(io.BytesIO(payload), chunk_bytes=chunk) == reference(payload, chunk)


@pytest.mark.parametrize('tail', [b'\0', b')', b'garbage', b'(exit', b'(assert "open)',
    b'(assert |open)', b'(assert |bad\\name|)', b'; nul\0', b'(assert "nul\0")',
    b'("bad-head" true)', b'(|assert| true)', b'()', b'(\xc3\xa9 true)', b'(assert true)'])
@pytest.mark.parametrize('chunk', [2, 37, 65536])
def test_invalid_tail_still_rejected(tail, chunk):
    payload = b'(declare-const x Bool)\n(assert x)\n(exit)\n' + tail
    with pytest.raises(validator.Rejected): reference(payload, chunk)
    with pytest.raises(validator.Rejected): validator.complete_envelope(io.BytesIO(payload), chunk_bytes=chunk)


def test_many_flat_and_nested_commands_use_bulk_counts():
    payload = b''.join(b'(declare-const x%d Bool)\n' % i for i in range(10000))
    payload += b'(assert (or x1 (not x2)))\n' * 10000 + b'(exit)\n'
    metrics = {}; result = validator.complete_envelope(io.BytesIO(payload), chunk_bytes=65536, metrics=metrics)
    assert result == reference(payload, 65536)
    assert metrics['fast_commands'] > 15000 and metrics['fallback_commands'] < 5000


def test_randomized_line_order_does_not_join_partial_commands():
    rng = random.Random(78412)
    lines = [b'(declare-const x Bool)\n', b'(assert (or x (not x)))\n', b'\n',
             b'(set-option :produce-models true)\r\n', b'(minimize (+ 1 2))\n']
    for _ in range(30):
        payload = b''.join(rng.choice(lines) for _ in range(60)) + b'(exit)'
        assert validator.complete_envelope(io.BytesIO(payload), chunk_bytes=313) == reference(payload, 313)
    for payload in [b'(asser\n(declare-const x Bool)\nt true)\n',
                    b'foo\n(assert true)\nbar', b'(assert\n(assert true)\n)\n']:
        try: expected = reference(payload, 11)
        except validator.Rejected:
            with pytest.raises(validator.Rejected): validator.complete_envelope(io.BytesIO(payload), chunk_bytes=11)
        else: assert validator.complete_envelope(io.BytesIO(payload), chunk_bytes=11) == expected


@pytest.mark.parametrize('suffix', [b'', b'\n; valid end'])
def test_compressed_hash_and_truncated_crc_are_checked(suffix):
    raw = b'(declare-const x Bool)\n(assert x)\n(exit)' + suffix
    packed = gzip.compress(raw, mtime=0)
    with gzip.GzipFile(fileobj=io.BytesIO(packed)) as f:
        assert validator.complete_envelope(f) == reference(raw, 13)
    with pytest.raises((EOFError, gzip.BadGzipFile)):
        with gzip.GzipFile(fileobj=io.BytesIO(packed[:-4])) as f: validator.complete_envelope(f)


def test_read_and_byte_accounting_reaches_actual_eof_once():
    class Reader(io.BytesIO):
        def __init__(self, raw): super().__init__(raw); self.empty_reads = 0
        def read(self, size):
            data = super().read(size)
            if not data: self.empty_reads += 1
            return data
    raw = b'(declare-const x Bool)\n' * 100 + b'(assert "fallback")\n(exit)\n'
    stream = Reader(raw); result = validator.complete_envelope(stream, chunk_bytes=111)
    assert stream.empty_reads == 1
    assert result['sha256'] == hashlib.sha256(raw).hexdigest() and result['bytes'] == len(raw)
