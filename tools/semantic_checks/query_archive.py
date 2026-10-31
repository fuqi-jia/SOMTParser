"""Archive an entire SMT query without full UTF-8 and gzip buffer copies."""
import gzip
import hashlib
import os
from pathlib import Path
import time
from .phase_events import timed_phase


class _ArchiveWriter:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.bytes = 0
        self.write_seconds = 0.0

    def write(self, data):
        started = time.perf_counter()
        written = self.stream.write(data)
        self.write_seconds += time.perf_counter() - started
        if written != len(data):
            raise OSError('incomplete compressed query write')
        self.digest.update(data)
        self.bytes += written
        return written

    def flush(self):
        started = time.perf_counter()
        self.stream.flush()
        self.write_seconds += time.perf_counter() - started


def archive_complete_query(solver, destination, *, chunk_chars=262144,
                           progress_callback=None):
    """Preserve every character of to_smt2(), with a complete gzip member.

    The chunk size controls only a temporary buffer, never the formula size.
    Z3 still creates its complete SMT string; this avoids the additional whole
    UTF-8 byte string and compressed byte string. Compression remains level 9.
    A failed write leaves its partial file, never a published complete archive.
    """
    if type(chunk_chars) is not int or chunk_chars <= 0:
        raise ValueError('chunk_chars must be a positive integer')
    destination = Path(destination)
    if destination.exists():
        raise FileExistsError(destination)
    partial = destination.with_name(destination.name + '.partial')
    if partial.exists():
        raise FileExistsError(partial)
    with timed_phase(progress_callback, 'complete-query-to-smt2'):
        text = solver.to_smt2()
        if not isinstance(text, str):
            raise TypeError('to_smt2 must return the complete query string')
    raw_digest = hashlib.sha256()
    raw_bytes = 0
    encode_seconds = 0.0
    gzip_write_seconds = 0.0
    # Character slices cannot split a Unicode code point. Concatenating their
    # UTF-8 encodings therefore gives exactly text.encode('utf-8').
    with partial.open('xb') as output:
        archive = _ArchiveWriter(output)
        with timed_phase(progress_callback, 'complete-query-utf8-gzip-write'):
            started = time.perf_counter()
            packed = gzip.GzipFile(filename='', mode='wb', compresslevel=9,
                                   fileobj=archive, mtime=0)
            gzip_write_seconds += time.perf_counter() - started
            try:
                for offset in range(0, len(text), chunk_chars):
                    started = time.perf_counter()
                    data = text[offset:offset + chunk_chars].encode('utf-8')
                    raw_digest.update(data)
                    raw_bytes += len(data)
                    encode_seconds += time.perf_counter() - started
                    started = time.perf_counter()
                    packed.write(data)
                    gzip_write_seconds += time.perf_counter() - started
            finally:
                started = time.perf_counter()
                packed.close()
                gzip_write_seconds += time.perf_counter() - started
        with timed_phase(progress_callback, 'complete-query-write-finalize'):
            archive.flush()
            output.close()
    # Publish only after GzipFile wrote its full trailer and the file closed.
    with timed_phase(progress_callback, 'complete-query-publish'):
        # Same-directory hard linking is an atomic no-replace publication.
        # An independently published complete file must never be overwritten.
        os.link(partial, destination)
        partial.unlink()
    return dict(path=str(destination), raw_sha256=raw_digest.hexdigest(),
                raw_bytes=raw_bytes, archive_sha256=archive.digest.hexdigest(),
                archive_bytes=archive.bytes,
                archive_profile=dict(chunk_chars=chunk_chars, compresslevel=9,
                    utf8_and_raw_hash_seconds=encode_seconds,
                    gzip_and_write_seconds=gzip_write_seconds,
                    file_write_seconds=archive.write_seconds))
