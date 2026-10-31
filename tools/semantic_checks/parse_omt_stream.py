"""Independent Z3 Optimize parsing without copying stored ASTs.

The old assertions()/objectives() calls were diagnostic counters, not checks.
Weighted-clause and objective correspondence remains the separate, pinned
streaming check. Hash the exact bytes fed to the parser pipe so its receipt
can be joined to that correspondence result. A successful from_file() call
may stop at (exit); source_eof records feeder EOF, not parser consumption.
The separate whole-input certificate must also reject post-exit content.
"""
from pathlib import Path
import hashlib
import json
import os
import resource
import sys
import subprocess
import tempfile
import gzip


def sha(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def set_worker_memory_limit(memory_bytes=2 * 1024 ** 3):
    """Use the 2 GiB default without exceeding an inherited RLIMIT_AS."""
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    limit = memory_bytes
    for inherited in (soft, hard):
        if inherited != resource.RLIM_INFINITY:
            limit = min(limit, inherited)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def validate_runtime(z3, manifest_path):
    expected = json.loads(Path(manifest_path).read_text())['tools']['independent_parser']
    assert Path(z3.__file__).resolve() == Path(expected['module']).resolve()
    assert sha(z3.__file__) == expected['module_sha256']
    libraries = {str(Path(line.split(maxsplit=5)[5]).resolve())
                 for line in Path('/proc/self/maps').read_text().splitlines()
                 if len(line.split(maxsplit=5)) == 6 and '/libz3.so' in line}
    assert libraries == {expected['library']}
    assert sha(expected['library']) == expected['library_sha256']
    assert z3.get_version_string() == expected['version']


def feed_stream(source_path, receipt_path, compressed=False):
    digest = hashlib.sha256()
    size = 0
    opener = gzip.open if compressed else open
    with opener(source_path, 'rb') as source:
        for block in iter(lambda: source.read(65536), b''):
            sys.stdout.buffer.write(block)
            digest.update(block)
            size += len(block)
    sys.stdout.buffer.flush()
    Path(receipt_path).write_text(json.dumps(dict(
        sha256=digest.hexdigest(), bytes=size, source_eof=True)) + '\n')


def parse_target(z3, source_path, compressed=False):
    # A thread can reserve an additional allocator arena and stack inside the
    # parser's AS limit. A separate bounded feeder keeps that reservation out
    # of Z3's address space, while preserving exact-byte hashing and EOF checks.
    with tempfile.TemporaryDirectory(prefix='somt-parser-feed-') as directory:
        receipt_path = Path(directory) / 'receipt.json'
        command = [sys.executable, '-B', str(Path(__file__).resolve()),
                   '--feed-gzip' if compressed else '--feed-plain',
                   str(source_path), str(receipt_path)]
        # Z3 may terminate natively (for example on memory exhaustion), bypassing
        # finally. The feeder must not inherit the parser's result-log descriptor:
        # a later BrokenPipe traceback would invalidate an already hashed log.
        # A nonzero feeder exit remains an explicit parse failure below.
        feeder = subprocess.Popen(command, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL)
        try:
            model = z3.Optimize()
            model.from_file(f'/proc/self/fd/{feeder.stdout.fileno()}')
        finally:
            feeder.stdout.close()
            try:
                feeder_rc = feeder.wait(timeout=10)
            except subprocess.TimeoutExpired:
                feeder.kill()
                feeder.wait()
                raise RuntimeError('input feeder did not terminate after parser EOF')
        if feeder_rc != 0:
            raise RuntimeError(f'input feeder failed: returncode={feeder_rc}')
        receipt = json.loads(receipt_path.read_text())
        if not receipt.get('source_eof'):
            raise RuntimeError('input feeder did not reach source EOF')
    return dict(parser='Z3 Optimize.from_file', version=z3.get_version_string(),
                parsed=True, target=receipt, feed='separate bounded process',
                parser_stop_policy='first exit or EOF',
                hash_scope='all bytes fed',
                complete_target_validation='requires matching structural certificate including EOF',
                assertion_objective_ast_vectors='not-materialized',
                count_validation='separate SHA-matched weighted-clause correspondence',
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


if __name__ == '__main__':
    set_worker_memory_limit()
    if sys.argv[1] in ('--feed-gzip', '--feed-plain'):
        feed_stream(sys.argv[2], sys.argv[3], compressed=sys.argv[1] == '--feed-gzip')
        raise SystemExit(0)
    import z3
    validate_runtime(z3, sys.argv[2])
    print(json.dumps(parse_target(z3, sys.argv[1], compressed='--gzip-target' in sys.argv[3:])))
