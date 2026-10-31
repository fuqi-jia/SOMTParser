"""Byte-exact streaming scanner checks against an independent frozen bytewise implementation."""
import gzip
import hashlib
import importlib.util
import io
from pathlib import Path
import random
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import validate_packed_smt_stream as scanner

# A historical reference is embedded below solely for differential checks.
Command, Rejected, SPACE = scanner.Command, scanner.Rejected, scanner.SPACE

def legacy_commands(stream, *, max_command_bytes, chunk_bytes=65536, budget_check=None):
    """Scan bytes without confusing delimiters inside strings/symbols/comments.

    In SMT-LIB strings, a doubled quote is an embedded quote; backslash is not
    an escape for a quote. A pending quote survives a chunk boundary. Quoted
    symbols cannot contain backslash. Byte offsets refer to decompressed input.
    """
    depth = 0
    state = 'normal'
    raw = bytearray()
    offset = 0
    line = 1
    index = 0
    start = start_line = 0
    for chunk in iter(lambda: stream.read(chunk_bytes), b''):
        if budget_check:
            budget_check()
        for ch in chunk:
            # Z3 receives a C string: an embedded NUL must never terminate
            # what it sees before the byte stream checked here has ended.
            # Reject it even in comments and after the final command.
            if ch == 0:
                command = (Command(index, start, offset + 1, start_line, bytes(raw) + b'\x00')
                           if depth else None)
                raise Rejected('NUL byte is unsupported', command, byte_offset=offset, line=line)
            if depth:
                raw.append(ch)
                if len(raw) > max_command_bytes:
                    raise Rejected('command byte budget exceeded',
                                   Command(index, start, offset + 1, start_line, bytes(raw)))
            if state == 'string_quote':
                if ch == 34:
                    state = 'string'
                    offset += 1
                    continue
                state = 'normal'
            if state == 'comment':
                if ch in (10, 13):
                    state = 'normal'
            elif state == 'string':
                if ch == 34:
                    state = 'string_quote'
            elif state == 'quoted':
                if ch == 92:
                    raise Rejected('backslash is not permitted in a quoted symbol',
                                   Command(index, start, offset + 1, start_line, bytes(raw)))
                if ch == 124:
                    state = 'normal'
            elif ch == 59:
                state = 'comment'
            elif ch in SPACE:
                pass
            elif ch == 40:
                if not depth:
                    index += 1
                    start, start_line = offset, line
                    raw = bytearray(b'(')
                depth += 1
            elif ch == 41:
                if not depth:
                    raise Rejected('unexpected closing parenthesis', byte_offset=offset, line=line)
                depth -= 1
                if not depth:
                    yield Command(index, start, offset + 1, start_line, bytes(raw))
                    raw.clear()
            elif not depth:
                raise Rejected('non-command token at top level', byte_offset=offset, line=line)
            elif ch == 34:
                state = 'string'
            elif ch == 124:
                state = 'quoted'
            if ch == 10:
                line += 1
            offset += 1
    if depth:
        raise Rejected('truncated command or unterminated string/quoted symbol',
                       Command(index, start, offset, start_line, bytes(raw)))


def legacy_tokens(raw):
    """Lex only for command heads, declared names, options, and :named guards."""
    i = 0
    while i < len(raw):
        ch = raw[i]
        if ch in SPACE:
            i += 1
        elif ch == 59:
            while i < len(raw) and raw[i] not in (10, 13):
                i += 1
        elif ch in (40, 41):
            yield 'paren', raw[i:i + 1]
            i += 1
        elif ch in (34, 124):
            end = i + 1
            while end < len(raw):
                if raw[end] == ch:
                    if ch == 34 and end + 1 < len(raw) and raw[end + 1] == ch:
                        end += 2
                        continue
                    break
                end += 1
            if end == len(raw):
                raise Rejected('unterminated token')
            yield ('string' if ch == 34 else 'quoted'), raw[i + 1:end]
            i = end + 1
        else:
            end = i + 1
            while end < len(raw) and raw[end] not in b'() \t\r\n;"|':
                end += 1
            yield 'atom', raw[i:end]
            i = end


CHUNKS = [1, 2, 3, 7, 31, 127, 65536]


def observed(function, payload, chunk_bytes, limit):
    reader = scanner.HashReader(io.BytesIO(payload))
    commands = []
    error = None
    try:
        for row in function(reader, max_command_bytes=limit, chunk_bytes=chunk_bytes):
            commands.append((row.index, row.start, row.end, row.line, row.raw))
    except Rejected as exc:
        row = exc.command
        error = (str(exc), dict(exc.details), None if row is None else
                 (row.index, row.start, row.end, row.line, row.raw))
    return commands, error, reader.complete, reader.bytes, reader.hash.hexdigest()


def compare(payload, size, limit=1000000):
    expected = observed(legacy_commands, payload, size, limit)
    actual = observed(scanner.commands, payload, size, limit)
    assert actual == expected
    for _, start, end, line, raw in actual[0]:
        assert payload[start:end] == raw
        assert line == 1 + payload.count(b'\n', 0, start)
        assert list(scanner.tokens(raw)) == list(legacy_tokens(raw))
    return actual


@pytest.mark.parametrize('chunk_bytes', CHUNKS)
@pytest.mark.parametrize('payload', [
    b'(assert (= (+ (* 3 x) (* (- 2) y)) 1))(check-sat)(exit)',
    b'\r\n;before(()|"\r(assert true)\n;after)\r\n(check-sat)\n(exit);EOF',
    b'(assert (= |q;(\n)| "a\n;()""quoted"""))\n(exit)',
    b'(assert (= "backslash\\" "backslash\\"))\n(exit)',
    b'(' * 200 + b'x' + b')' * 200 + b'\n(exit)',
    b'(assert (= (+ ' + b'(ite b 99999999999999999999 0) ' * 2000 + b') 0))\n(exit)',
    b'(assert ;inside with )\r\n true)\n(check-sat)\n(exit)',
    b'(assert (= "" ""))\n(exit)',
])
def test_bulk_scanner_preserves_commands_receipts_and_tokens(chunk_bytes, payload):
    rows, error, complete, size, digest = compare(payload, chunk_bytes)
    assert rows and error is None and complete
    assert size == len(payload) and digest == hashlib.sha256(payload).hexdigest()


@pytest.mark.parametrize('chunk_bytes', CHUNKS)
@pytest.mark.parametrize('suffix', [
    b')', b'garbage', b'(', b'(assert "open)', b'(assert |open)',
    b'(assert |bad\\name|)', b';tail\x00', b'(assert "nul\x00")',
    b'(assert |nul\x00|)', b'(assert ;nul\x00\n true)', b'(assert "a""',
    b'\x0b', b'(assert true))', b'(assert true)\x00',
])
def test_lexical_damage_keeps_first_error_and_exact_prefix(chunk_bytes, suffix):
    payload = b'(assert true)\n(check-sat)\n(exit)\n' + suffix
    assert compare(payload, chunk_bytes)[1] is not None


@pytest.mark.parametrize('chunk_bytes', CHUNKS)
@pytest.mark.parametrize('limit', [1, 2, 5, 13, 14, 17, 18, 1.5])
def test_byte_budget_applies_inside_bulk_islands_with_identical_prefix(chunk_bytes, limit):
    compare(b'(assert (= x 123))\n(exit)', chunk_bytes, limit)
    compare(b'(assert "a\x00")', chunk_bytes, limit)
    compare(b'(assert |bad\\name|)', chunk_bytes, limit)


@pytest.mark.parametrize('chunk_bytes', [1, 7, 127, 65536])
def test_randomized_lexical_fragments_match_historical_machine(chunk_bytes):
    randomizer = random.Random(78217)
    fragments = [b'(', b')', b' ', b'\t', b'\r', b'\n', b'"', b'|', b';',
                 b'\\', b'abc', b':named', b'123', b'\x00', b'\xc3\xa9']
    for _ in range(160):
        data = b''.join(randomizer.choice(fragments) for _ in range(randomizer.randrange(1, 50)))
        compare(data, chunk_bytes, randomizer.choice([3, 17, 10000]))


@pytest.mark.parametrize('token', [b'"a""', b'"', b'|', b'"a""b', b'|abc'])
def test_fast_token_search_preserves_unterminated_token_failure(token):
    for function in (legacy_tokens, scanner.tokens):
        with pytest.raises(Rejected, match='unterminated token'):
            list(function(token))


def test_budget_callback_remains_once_per_read_and_hash_requires_real_eof():
    data = b'(assert true)\n(exit)\n;comment only'
    reader = scanner.HashReader(io.BytesIO(data))
    calls = []
    rows = list(scanner.commands(reader, max_command_bytes=1000, chunk_bytes=7,
                                 budget_check=lambda: calls.append(reader.bytes)))
    assert len(rows) == 2 and reader.complete
    assert calls == [min(n, len(data)) for n in range(7, len(data) + 7, 7)]
    assert reader.hash.hexdigest() == hashlib.sha256(data).hexdigest()


def test_gzip_crc_and_truncation_are_still_checked_after_final_exit():
    data = gzip.compress(b'(assert true)(check-sat)(exit);tail', mtime=0)
    for compressed in (data[:-1], data[:-8], data[:-8] + bytes([data[-8] ^ 1]) + data[-7:]):
        with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
            reader = scanner.HashReader(stream)
            with pytest.raises((EOFError, OSError)):
                list(scanner.commands(reader, max_command_bytes=1000, chunk_bytes=3))
            assert reader.complete is False
