#!/usr/bin/env python3
"""Validate a restricted SMT module in bounded, independent Z3 processes.

This is NOT a whole-module parse or a satisfiability/optimization check. Every
assertion and objective is parsed under the complete, closed declaration prefix.
The prefix is reparsed in each child; no assertion AST survives a child process.

Supported order: optional set-logic/options, declare-sort/define-sort,
declare-const/declare-fun/define-fun (in dependency order), assertions, objectives,
check-sat, optional get-model/get-objectives, mandatory exit. Declarations and
definitions may interleave. Stateful commands, recursive/datatype declarations,
soft assertions, term :named attributes, late declarations, duplicate names,
unknown commands/options, and trailing commands are explicitly rejected.
Query-tail commands are checked against this exact grammar, never executed.

Linux/POSIX only. Input can be plain SMT-LIB or gzip (detected by magic bytes).
The output directory must not exist. A report and append-only batch receipts are
written there, including failures. No source file is changed.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
import errno
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time


PREFIX = {'declare-sort', 'define-sort', 'declare-const', 'declare-fun', 'define-fun'}
BODY = {'assert', 'minimize', 'maximize'}
TAIL = {'check-sat', 'get-model', 'get-objectives', 'exit'}
SPACE = b' \t\r\n'


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, value):
    with Path(path).open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2, sort_keys=True, ensure_ascii=False)
        stream.write('\n')


@dataclass
class Command:
    index: int
    start: int
    end: int
    line: int
    raw: bytes

    def receipt(self):
        return dict(index=self.index, start_byte=self.start, end_byte=self.end,
                    line=self.line, bytes=len(self.raw), sha256=hashlib.sha256(self.raw).hexdigest())


class Rejected(ValueError):
    def __init__(self, message, command=None, **details):
        super().__init__(message)
        self.command = command
        self.details = details


class HashReader:
    def __init__(self, stream):
        self.stream = stream
        self.hash = hashlib.sha256()
        self.bytes = 0
        self.complete = False

    def read(self, size):
        data = self.stream.read(size)
        self.hash.update(data)
        self.bytes += len(data)
        if not data:
            self.complete = True
        return data


# The first alternative is a balanced island of depth at most two. Its leaves
# exclude every lexical delimiter, so skipping it preserves depth and state.
# Regex input is one bounded chunk, never an entire large command. The leaf and
# parenthesized alternatives are disjoint; there is no nested ambiguous `.*`.
_NORMAL_EVENT = re.compile(rb'\([^();"|\x00]*(?:\([^();"|\x00]*\)[^();"|\x00]*)*\)|\(+|\)+|[;"|\x00]')
_STATE_EVENT = {'comment': re.compile(rb'[\r\n\x00]'),
                'string': re.compile(rb'["\x00]'),
                'quoted': re.compile(rb'[|\\\x00]')}
_NON_SPACE = re.compile(rb'[^ \t\r\n]')
_TOKEN_END = re.compile(rb'[() \t\r\n;"|]')
_LINE_END = re.compile(rb'[\r\n]')


def commands(stream, *, max_command_bytes, chunk_bytes=65536, budget_check=None):
    """Scan complete commands with bulk C-level searches and exact byte receipts.

    Strings use doubled quotes, not backslash escaping. Pending quotes and all
    lexical states survive arbitrary read boundaries. NUL is rejected even in
    comments or after exit. Balanced delimiter-free islands need no per-byte
    Python work; all other parentheses use the ordinary depth machine.
    """
    depth, state = 0, 'normal'
    raw = bytearray()
    offset, line, index = 0, 1, 0
    start = start_line = 0
    for chunk in iter(lambda: stream.read(chunk_bytes), b''):
        if budget_check:
            budget_check()
        pos, length = 0, len(chunk)
        segment = 0 if depth else None

        def command_prefix(end):
            return bytes(raw) + chunk[segment:end]

        def check_size(end):
            if segment is not None and len(raw) + end - segment > max_command_bytes:
                # Retain exactly the first offending byte, not the rest of a
                # regex match/chunk. This matches the bytewise failure receipt.
                stop = segment + math.floor(max_command_bytes) - len(raw) + 1
                raise Rejected('command byte budget exceeded',
                               Command(index, start, offset + stop, start_line, command_prefix(stop)))

        while pos < length:
            if state == 'string_quote':
                if chunk[pos] == 34:
                    check_size(pos + 1)
                    state = 'string'
                    pos += 1
                    continue
                state = 'normal'
            pattern = _NORMAL_EVENT if state == 'normal' else _STATE_EVENT[state]
            event = pattern.search(chunk, pos)
            end = event.start() if event else length
            if state == 'normal' and not depth:
                bad = _NON_SPACE.search(chunk, pos, end)
                if bad:
                    at = bad.start()
                    raise Rejected('non-command token at top level', byte_offset=offset + at,
                                   line=line + chunk.count(b'\n', pos, at))
            check_size(end)
            if end > pos:
                line += chunk.count(b'\n', pos, end)
            pos = end
            if event is None:
                break
            ch, end = chunk[pos], event.end()
            if ch == 0:
                command = (Command(index, start, offset + pos + 1, start_line, command_prefix(pos + 1))
                           if depth else None)
                raise Rejected('NUL byte is unsupported', command, byte_offset=offset + pos, line=line)
            if state != 'normal':
                check_size(end)
                if state == 'comment':
                    state = 'normal'  # The event is CR or LF; NUL was handled above.
                elif state == 'string':
                    state = 'string_quote'
                elif ch == 92:
                    raise Rejected('backslash is not permitted in a quoted symbol',
                                   Command(index, start, offset + end, start_line, command_prefix(end)))
                else:
                    state = 'normal'
                line += ch == 10
                pos = end
                continue
            if ch == 40:
                if not depth:
                    index += 1
                    start, start_line, segment = offset + pos, line, pos
                check_size(end)
                if chunk[end - 1] == 41:  # A fully balanced lexical island.
                    line += chunk.count(b'\n', pos, end)
                    if not depth:
                        raw.extend(chunk[segment:end])
                        segment = None
                        yield Command(index, start, offset + end, start_line, bytes(raw))
                        raw.clear()
                else:  # A run containing only opening parentheses.
                    depth += end - pos
            elif ch == 41:
                if not depth:
                    raise Rejected('unexpected closing parenthesis', byte_offset=offset + pos, line=line)
                end = min(end, pos + depth)
                check_size(end)
                depth -= end - pos
                if not depth:
                    raw.extend(chunk[segment:end])
                    segment = None
                    yield Command(index, start, offset + end, start_line, bytes(raw))
                    raw.clear()
                # Surplus ')' from the same run are processed at the next pos.
            else:
                check_size(end)
                if ch == 59:
                    state = 'comment'
                elif not depth:
                    raise Rejected('non-command token at top level', byte_offset=offset + pos, line=line)
                else:
                    state = 'string' if ch == 34 else 'quoted'
            pos = end
        if depth:
            raw.extend(chunk[segment:length])
        offset += length
    if depth:
        raise Rejected('truncated command or unterminated string/quoted symbol',
                       Command(index, start, offset, start_line, bytes(raw)))


def tokens(raw):
    """Lex only for command heads, declared names, options, and :named guards."""
    i, length = 0, len(raw)
    while i < length:
        ch = raw[i]
        if ch in SPACE:
            match = _NON_SPACE.search(raw, i)
            i = match.start() if match else length
        elif ch == 59:
            match = _LINE_END.search(raw, i)
            i = match.start() if match else length
        elif ch in (40, 41):
            yield 'paren', raw[i:i + 1]
            i += 1
        elif ch in (34, 124):
            delimiter, end = raw[i:i + 1], i + 1
            while True:
                end = raw.find(delimiter, end)
                if end < 0:
                    raise Rejected('unterminated token')
                if ch == 34 and end + 1 < length and raw[end + 1] == ch:
                    end += 2
                    continue
                break
            yield ('string' if ch == 34 else 'quoted'), raw[i + 1:end]
            i = end + 1
        else:
            match = _TOKEN_END.search(raw, i)
            end = match.start() if match else length
            yield 'atom', raw[i:end]
            i = end


def command_head(command):
    ts = tokens(command.raw)
    assert next(ts) == ('paren', b'(')
    kind, value = next(ts, ('missing', b''))
    if kind != 'atom':
        raise Rejected('command head must be an unquoted symbol', command)
    try:
        return value.decode('ascii'), ts
    except UnicodeDecodeError:
        raise Rejected('unsupported non-ASCII command head', command) from None


# Envelope-only fast path. These expressions recognize entire physical lines,
# excluding every stateful lexical delimiter. A bounded nesting grammar is only
# a sufficient condition; everything else retains the general scanner below.
_ENVELOPE_LEAF = rb'[^();"|\x00\r\n]*'
_ENVELOPE_BODY = _ENVELOPE_LEAF
for _envelope_depth in range(3):
    _ENVELOPE_BODY = _ENVELOPE_LEAF + rb'(?:\(' + _ENVELOPE_BODY + rb'\)' + _ENVELOPE_LEAF + rb')*'
_ENVELOPE_LINE_PATTERNS = tuple(
    (head, re.compile(rb'^[ \t]*\(' + head.encode('ascii') + rb'(?=[() \t\r\n;"|])'
                      + _ENVELOPE_BODY + rb'\)[ \t]*(?:\r?\n|\Z)', re.MULTILINE))
    for head in ('declare-const', 'assert', 'declare-fun', 'set-logic', 'set-option',
                 'minimize', 'maximize', 'check-sat', 'get-model', 'get-objectives'))


class _EnvelopePrefixReader:
    """Replay already-hashed bytes exactly once before continuing the raw reader."""
    def __init__(self, prefix, reader):
        self.prefix = prefix
        self.position = 0
        self.reader = reader

    def read(self, size):
        if self.position < len(self.prefix):
            end = min(len(self.prefix), self.position + size)
            data = self.prefix[self.position:end]
            self.position = end
            return data
        return self.reader.read(size)


def complete_envelope(stream, *, chunk_bytes=1024 * 1024, metrics=None):
    """Audit every raw byte and top-level command without parsing SMT semantics.

    Canonical delimiter-free lines are validated and counted in C-level regex
    passes instead of allocating a Command/token generator for each declaration.
    No removed line can join two partial lines: matches consume whole lines and
    their final newline. Commands containing lexical delimiters, multiline or
    deeper terms, unknown heads, and the exit tail use the original scanner.
    Its full remaining stream is replayed without hashing the prefix twice.
    A successful report always includes an actual empty read and gzip EOF/CRC.
    """
    if chunk_bytes <= 0:
        raise ValueError('chunk_bytes must be positive')
    reader = HashReader(stream)
    heads = Counter()
    pending = b''
    fast_count = 0
    while True:
        chunk = reader.read(chunk_bytes)
        data = pending + chunk
        if chunk:
            end = data.rfind(b'\n') + 1
            # A huge or multiline command is handled by the existing scanner,
            # not accumulated in an unbounded speculative fast-path buffer.
            if end == 0:
                prefix = data
                break
            block, pending = data[:end], data[end:]
        else:
            block, pending = data, b''
        remainder = block
        counts = {}
        for head, pattern in _ENVELOPE_LINE_PATTERNS:
            remainder, count = pattern.subn(b'', remainder)
            if count:
                counts[head] = count
        if remainder.strip(SPACE):
            prefix = block + pending
            break
        heads.update(counts)
        fast_count += sum(counts.values())
        if not chunk:
            if metrics is not None:
                metrics.update(fast_commands=fast_count, fallback_commands=0)
            return {'complete_eof': True, 'sha256': reader.hash.hexdigest(),
                    'bytes': reader.bytes, 'commands': dict(heads)}
    exited = False
    fallback_count = 0
    replay = _EnvelopePrefixReader(prefix, reader)
    for command in commands(replay, max_command_bytes=float('inf')):
        if exited:
            raise Rejected('non-comment content after exit', command)
        name, _ = command_head(command)
        heads[name] += 1
        fallback_count += 1
        exited = name == 'exit'
    if not reader.complete:
        raise Rejected('incomplete target envelope')
    if metrics is not None:
        metrics.update(fast_commands=fast_count, fallback_commands=fallback_count)
    return {'complete_eof': True, 'sha256': reader.hash.hexdigest(),
            'bytes': reader.bytes, 'commands': dict(heads)}


def loaded_z3_library():
    """Fingerprint the actual mapped library, independent of z3py internals."""
    paths = set()
    for line in Path('/proc/self/maps').read_text().splitlines():
        fields = line.split(None, 5)
        if len(fields) != 6:
            continue
        path = re.sub(r'\\([0-7]{3})', lambda match: chr(int(match.group(1), 8)), fields[5])
        if re.search(r'/libz3\.so(?:\.[0-9.]+)?(?: \(deleted\))?$', path):
            if path.endswith(' (deleted)'):
                raise ValueError('loaded Z3 library was deleted')
            paths.add(Path(path).resolve(strict=True))
    if len(paths) != 1:
        raise ValueError('expected exactly one mapped libz3 library: ' + str(sorted(map(str, paths))))
    return paths.pop()


def _worker(config_path):
    config = json.loads(Path(config_path).read_text())
    resource.setrlimit(resource.RLIMIT_AS, (config['memory_bytes'], config['memory_bytes']))
    resource.setrlimit(resource.RLIMIT_CPU, (config['cpu_seconds'], config['cpu_seconds']))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    result = dict(ok=False, solver_check=False)
    try:
        import z3
        library = loaded_z3_library()
        runtime = dict(version=z3.get_version_string(), library=str(library),
                       library_sha256=digest(library), module=str(Path(z3.__file__).resolve()),
                       module_sha256=digest(z3.__file__))
        result['runtime'] = runtime
        for key, wanted in config.get('expected_runtime', {}).items():
            if wanted is not None and runtime[key] != wanted:
                raise ValueError(f'Z3 runtime mismatch for {key}: {runtime[key]} != {wanted}')
        prefix = Path(config['prefix']).read_bytes()
        batch = Path(config['batch']).read_bytes()
        text = (prefix + batch).decode('utf-8', errors='strict')
        optimizer = z3.Optimize()
        optimizer.from_string(text)
        result.update(ok=True, assertions=len(optimizer.assertions()), objectives=len(optimizer.objectives()))
        if result['assertions'] != config['assertions'] or result['objectives'] != config['objectives']:
            result.update(ok=False, error='Z3 parsed command counts differ from submitted counts')
    except Exception as exc:
        result.update(error=type(exc).__name__ + ': ' + str(exc)[:16384])
    write_json(config['result'], result)
    return 0 if result['ok'] else 1


class Validator:
    def __init__(self, source, output, *, batch_commands=50000, batch_bytes=4 * 1024 * 1024,
                 max_command_bytes=16 * 1024 * 1024, max_prefix_bytes=32 * 1024 * 1024,
                 memory_bytes=2 * 1024 ** 3, batch_seconds=120, total_seconds=900, total_cpu_seconds=600,
                 expected_version=None, expected_library_sha256=None):
        self.source, self.output = Path(source), Path(output)
        self.limits = dict(batch_commands=batch_commands, batch_bytes=batch_bytes,
                           max_command_bytes=max_command_bytes, max_prefix_bytes=max_prefix_bytes,
                           memory_bytes=memory_bytes, batch_seconds=batch_seconds, total_seconds=total_seconds,
                           total_cpu_seconds=total_cpu_seconds)
        if any(isinstance(v, bool) or not isinstance(v, (int, float)) or v <= 0 for v in self.limits.values()):
            raise ValueError('all budgets must be positive')
        self.expected_runtime = dict(version=expected_version, library_sha256=expected_library_sha256)
        self.counts = Counter()
        self.coverage = hashlib.sha256()
        self.start = time.monotonic()
        usage = resource.getrusage(resource.RUSAGE_SELF)
        self.cpu_start = usage.ru_utime + usage.ru_stime
        self.batch_count = self.parsed_assertions = self.parsed_objectives = 0
        self.child_cpu = 0.0
        self.child_peak = 0
        self.prefix_commands = []
        self.prefix_size = self.prefix_lines = 0
        self.batch = []
        self.batch_size = 0
        self.last = None
        self.phase = 'prefix'
        self.declared = set()
        self.options = set()
        self.queries = set()
        self.saw_logic = False
        self.prefix_checked = False
        self.reader = None
        self.input_record = {}

    def elapsed(self):
        return time.monotonic() - self.start

    def parent_cpu(self):
        usage = resource.getrusage(resource.RUSAGE_SELF)
        return usage.ru_utime + usage.ru_stime - self.cpu_start

    def _budget(self, active_pid=None):
        if self.elapsed() >= self.limits['total_seconds']:
            raise Rejected('total wall time budget exceeded', self.last)
        active_cpu = 0.0
        if active_pid is not None:
            try:
                # Linux process totals include all threads. Children have no
                # grandchildren, and wait4 supplies their final exact usage.
                fields = Path(f'/proc/{active_pid}/stat').read_text().rsplit(')', 1)[1].split()
                active_cpu = (int(fields[11]) + int(fields[12])) / os.sysconf('SC_CLK_TCK')
            except OSError as error:
                if error.errno not in (errno.ENOENT, errno.ESRCH):
                    raise
                # It exited between wait4(WNOHANG) and the procfs open/read.
        if self.parent_cpu() + self.child_cpu + active_cpu >= self.limits['total_cpu_seconds']:
            raise Rejected('total cumulative CPU budget exceeded', self.last)

    def _run_batch(self, commands_in_batch, *, prefix_only=False):
        self._budget()
        number = self.batch_count + 1
        batch_path = self.work / 'batch.smt2'
        with batch_path.open('wb') as stream:
            for command in commands_in_batch:
                stream.write(command.raw + b'\n')
        result_path = self.work / f'result-{number}.json'
        config_path = self.work / 'worker.json'
        expected_assertions = sum(command_head(c)[0] == 'assert' for c in commands_in_batch)
        expected_objectives = len(commands_in_batch) - expected_assertions
        remaining_cpu = self.limits['total_cpu_seconds'] - self.parent_cpu() - self.child_cpu
        config = dict(prefix=str(self.output / 'prefix.smt2'), batch=str(batch_path),
                      result=str(result_path), memory_bytes=self.limits['memory_bytes'],
                      cpu_seconds=max(1, math.ceil(min(self.limits['batch_seconds'], remaining_cpu))),
                      assertions=expected_assertions, objectives=expected_objectives,
                      expected_runtime=self.expected_runtime)
        config_path.write_text(json.dumps(config))
        wall_limit = min(self.limits['batch_seconds'], self.limits['total_seconds'] - self.elapsed())
        started = time.monotonic()
        log_path = self.work / 'worker.log'
        with log_path.open('wb') as log:
            proc = subprocess.Popen([sys.executable, '-B', str(Path(__file__).resolve()), '--worker', str(config_path)],
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            cumulative_budget_error = None
            while True:
                pid, status, usage = os.wait4(proc.pid, os.WNOHANG)
                if pid:
                    break
                try:
                    self._budget(proc.pid)
                except Rejected as exc:
                    cumulative_budget_error = str(exc)
                if cumulative_budget_error or time.monotonic() - started >= wall_limit:
                    timed_out = time.monotonic() - started >= wall_limit
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    _, status, usage = os.wait4(proc.pid, 0)
                    break
                time.sleep(.01)
            proc.returncode = os.waitstatus_to_exitcode(status)
        try:
            result = json.loads(result_path.read_text()) if result_path.exists() else dict(ok=False, error='worker exited without receipt')
        except (ValueError, UnicodeError) as exc:
            result = dict(ok=False, error='invalid worker receipt: ' + str(exc))
        self.batch_count += 1
        self.child_cpu += usage.ru_utime + usage.ru_stime
        self.child_peak = max(self.child_peak, usage.ru_maxrss)
        row = dict(batch=number, prefix_only=prefix_only, command_count=len(commands_in_batch),
                   first_command=commands_in_batch[0].index if commands_in_batch else None,
                   last_command=commands_in_batch[-1].index if commands_in_batch else None,
                   body_bytes=batch_path.stat().st_size, body_sha256=digest(batch_path),
                   result=result, returncode=proc.returncode, wall_timeout=timed_out,
                   cumulative_budget_error=cumulative_budget_error,
                   worker_log_bytes=log_path.stat().st_size, worker_log_sha256=digest(log_path),
                   wall_seconds=time.monotonic() - started, user_seconds=usage.ru_utime,
                   system_seconds=usage.ru_stime, peak_rss_kib=usage.ru_maxrss)
        if log_path.stat().st_size:
            shutil.copyfile(log_path, self.output / f'batch-{number:06d}.log')
        with (self.output / 'batches.jsonl').open('a') as stream:
            stream.write(json.dumps(row, sort_keys=True) + '\n'); stream.flush(); os.fsync(stream.fileno())
        if proc.returncode != 0 or timed_out or cumulative_budget_error or not result.get('ok'):
            shutil.copyfile(batch_path, self.output / 'failure-batch.smt2')
            shutil.copyfile(log_path, self.output / 'failure-worker.log')
            if result_path.exists():
                shutil.copyfile(result_path, self.output / 'failure-worker-receipt.json')
            command = None
            match = re.search(r'line (\d+) column', result.get('error', ''))
            if match:
                failed_line = int(match.group(1))
                line = 1
                for candidate in [*self.prefix_commands, *commands_in_batch]:
                    end_line = line + candidate.raw.count(b'\n')
                    if line <= failed_line <= end_line:
                        command = candidate
                        break
                    line = end_line + 1
            raise Rejected('Z3 batch parse failed', command, failed_batch=row)
        self._budget()
        runtime = result['runtime']
        self.expected_runtime = runtime
        self.parsed_assertions += expected_assertions
        self.parsed_objectives += expected_objectives
        result_path.unlink()

    def _flush(self):
        if self.batch:
            self._run_batch(self.batch)
            self.batch.clear()
            self.batch_size = 0

    def _close_prefix(self):
        if not self.prefix_checked:
            self.prefix_stream.flush()
            self._run_batch([], prefix_only=True)
            self.prefix_checked = True

    def _consume(self, command):
        self.last = command
        if command.index % 1024 == 0:
            self._budget()
        head, ts = command_head(command)
        self.counts[head] += 1
        self.coverage.update(struct.pack('>QQQ', command.index, command.start, command.end))
        self.coverage.update(hashlib.sha256(command.raw).digest())
        if b':named' in command.raw and any(kind == 'atom' and value == b':named' for kind, value in tokens(command.raw)):
            raise Rejected(':named introduces cross-command state and is unsupported', command)
        if head in PREFIX or head in {'set-logic', 'set-option'}:
            if self.phase != 'prefix':
                raise Rejected('late declaration, definition, or option', command)
            if head in PREFIX:
                kind, name = next(ts, ('missing', b''))
                if kind not in {'atom', 'quoted'}:
                    raise Rejected('declared name must be a symbol', command)
                if name in self.declared:
                    raise Rejected('duplicate declared name: ' + name.decode('utf-8', 'replace'), command)
                self.declared.add(name)
            else:
                if self.declared:
                    raise Rejected('set-logic/options must precede declarations', command)
                parts = list(tokens(command.raw))
                if head == 'set-logic':
                    if self.saw_logic or len(parts) != 4 or parts[2][0] != 'atom':
                        raise Rejected('invalid or repeated set-logic', command)
                    self.saw_logic = True
                else:
                    allowed = {b':produce-models': {b'true', b'false'},
                               b':opt.priority': {b'lex', b'pareto', b'box'}}
                    if (len(parts) != 5 or parts[2][0] != 'atom' or parts[3][0] != 'atom'
                            or parts[2][1] not in allowed or parts[3][1] not in allowed[parts[2][1]]
                            or parts[2][1] in self.options):
                        raise Rejected('unsupported, malformed, or repeated set-option', command)
                    self.options.add(parts[2][1])
            self.prefix_size += len(command.raw) + 1
            if self.prefix_size > self.limits['max_prefix_bytes']:
                raise Rejected('prefix byte budget exceeded', command)
            self.prefix_stream.write(command.raw + b'\n')
            self.prefix_commands.append(command)
            return
        self._close_prefix()
        if head in BODY:
            if self.phase == 'tail' or self.phase == 'done' or (head == 'assert' and self.phase == 'objectives'):
                raise Rejected('assertion/objective after its permitted phase', command)
            self.phase = 'assertions' if head == 'assert' else 'objectives'
            size = len(command.raw) + 1
            if size > self.limits['batch_bytes']:
                raise Rejected('single body command exceeds batch byte budget', command)
            if self.batch and (len(self.batch) >= self.limits['batch_commands']
                               or self.batch_size + size > self.limits['batch_bytes']):
                self._flush()
            self.batch.append(command)
            self.batch_size += size
        elif head in TAIL:
            if list(tokens(command.raw)) != [('paren', b'('), ('atom', head.encode()), ('paren', b')')]:
                raise Rejected('tail command must have no arguments', command)
            if self.phase == 'done' or head in self.queries:
                raise Rejected('repeated command or command after exit', command)
            if head != 'check-sat' and 'check-sat' not in self.queries:
                raise Rejected('query tail requires check-sat first', command)
            self._flush()
            self.queries.add(head)
            self.phase = 'done' if head == 'exit' else 'tail'
        else:
            raise Rejected('unsupported command: ' + head, command)

    def run(self):
        self.output.mkdir(parents=True, exist_ok=False)
        (self.output / 'batches.jsonl').touch(exist_ok=False)
        self.input_record = dict(path=str(self.source.resolve()), bytes=self.source.stat().st_size,
                                 sha256=digest(self.source))
        report = dict(schema='somt-packed-smt-stream-v1', ok=False, whole_module_parse=False,
                      all_asts_resident_together=False, solver_check=False,
                      tail_validation='strict grammar only; query commands are never executed',
                      budgets=self.limits, input=self.input_record, tool_sha256=digest(__file__))
        try:
            with tempfile.TemporaryDirectory(prefix='.worker-', dir=self.output) as temporary:
                self.work = Path(temporary)
                with self.source.open('rb') as raw, (self.output / 'prefix.smt2').open('xb') as self.prefix_stream:
                    magic = raw.read(2); raw.seek(0)
                    compressed = magic == b'\x1f\x8b'
                    report['gzip'] = compressed
                    stream = gzip.GzipFile(fileobj=raw) if compressed else raw
                    try:
                        self.reader = HashReader(stream)
                        for command in commands(self.reader, max_command_bytes=self.limits['max_command_bytes'],
                                                budget_check=self._budget):
                            self._consume(command)
                        self._close_prefix()
                        self._flush()
                        if self.phase != 'done':
                            raise Rejected('missing mandatory check-sat/exit tail', self.last)
                    finally:
                        if compressed:
                            stream.close()
                if digest(self.source) != self.input_record['sha256']:
                    raise Rejected('source changed while validating')
                self._budget()
                if self.parsed_assertions != self.counts['assert'] or self.parsed_objectives != self.counts['minimize'] + self.counts['maximize']:
                    raise Rejected('incomplete command coverage')
                report['ok'] = True
        except Exception as exc:
            report['error'] = type(exc).__name__ + ': ' + str(exc)
            if isinstance(exc, Rejected):
                report.update(exc.details)
                if exc.command:
                    report['failed_command'] = exc.command.receipt()
                    (self.output / 'failure-command.smt2').write_bytes(exc.command.raw)
        report.update(command_counts=dict(self.counts), commands=sum(self.counts.values()),
                      assertions=self.counts['assert'], objectives=self.counts['minimize'] + self.counts['maximize'],
                      parsed_assertions=self.parsed_assertions, parsed_objectives=self.parsed_objectives,
                      prefix_commands=len(self.prefix_commands), prefix_bytes=self.prefix_size,
                      prefix_sha256=digest(self.output / 'prefix.smt2') if (self.output / 'prefix.smt2').exists() else None,
                      batches=self.batch_count, child_cpu_seconds=self.child_cpu,
                      controller_cpu_seconds=self.parent_cpu(),
                      total_cpu_seconds=self.parent_cpu() + self.child_cpu,
                      child_peak_rss_kib=self.child_peak, controller_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      rss_peak_sum_upper_bound_kib=self.child_peak + resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      elapsed_seconds=self.elapsed(), coverage_sha256=self.coverage.hexdigest(), runtime=self.expected_runtime)
        if self.reader:
            report['decoded_input'] = dict(bytes=self.reader.bytes, sha256=self.reader.hash.hexdigest(),
                                           complete=self.reader.complete)
        write_json(self.output / 'report.json', report)
        return report


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == '--worker':
        return _worker(argv[1])
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    for name, default in [('batch-commands', 50000), ('batch-bytes', 4 * 1024 * 1024),
                          ('max-command-bytes', 16 * 1024 * 1024), ('max-prefix-bytes', 32 * 1024 * 1024),
                          ('memory-bytes', 2 * 1024 ** 3), ('batch-seconds', 120), ('total-seconds', 900),
                          ('total-cpu-seconds', 600)]:
        parser.add_argument('--' + name, type=int, default=default)
    parser.add_argument('--expected-version')
    parser.add_argument('--expected-library-sha256')
    args = vars(parser.parse_args(argv))
    source, output = args.pop('source'), args.pop('output')
    resource.setrlimit(resource.RLIMIT_AS, (args['memory_bytes'], args['memory_bytes']))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_CPU, (args['total_cpu_seconds'], args['total_cpu_seconds']))
    report = Validator(source, output, **args).run()
    print(json.dumps(report, sort_keys=True))
    return 0 if report['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
