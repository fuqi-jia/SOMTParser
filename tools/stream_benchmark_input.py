#!/usr/bin/env python3
"""Stream a plain/compressed benchmark to stdout, recording completed decoding.

The caller must require a zero exit code AND a complete receipt, alongside the
converter's result. A converter can accept a valid prefix of a damaged archive.
Resource limits and pipeline cancellation are the caller's responsibility.
"""
import argparse
import bz2
import gzip
import hashlib
import json
import lzma
from pathlib import Path
import sys


OPENERS = {'.gz': gzip.open, '.xz': lzma.open, '.lzma': lzma.open, '.bz2': bz2.open}
BLOCK_BYTES = 1024 * 1024


def strict_members(source):
    """Decode concatenated bzip2/LZMA members without ignoring trailing junk.

    Python's BZ2File/LZMAFile deliberately ignore invalid bytes after a valid
    member. Use their incremental decoders to verify every member instead.
    XZ stream padding is allowed only in multiples of four zero bytes.
    """
    with source.open('rb') as raw:
        pending = raw.read(BLOCK_BYTES)
        xz = pending.startswith(b'\xfd7zXZ\x00')
        make_decoder = bz2.BZ2Decompressor if source.suffix.lower() == '.bz2' else (
            lambda: lzma.LZMADecompressor(format=lzma.FORMAT_XZ if xz else lzma.FORMAT_ALONE))
        if not pending:
            raise EOFError('empty compressed input')
        decoder = make_decoder()
        while True:
            block = decoder.decompress(pending, max_length=BLOCK_BYTES)
            pending = b''
            if block:
                yield block
            if decoder.eof:
                pending = decoder.unused_data
                padding = 0
                while True:
                    if not pending:
                        pending = raw.read(BLOCK_BYTES)
                    if xz:
                        stripped = pending.lstrip(b'\x00')
                        padding += len(pending) - len(stripped)
                        if pending and not stripped:
                            pending = b''
                            continue
                        pending = stripped
                        if padding % 4:
                            raise ValueError('XZ stream padding must contain a multiple of four zero bytes')
                    if not pending:
                        return
                    break
                decoder = make_decoder()
            elif decoder.needs_input:
                pending = raw.read(BLOCK_BYTES)
                if not pending:
                    raise EOFError('truncated compressed member')


def stream_source(source, output, receipt):
    source, receipt = Path(source), Path(receipt)
    result = {'source': str(source), 'compression': source.suffix.lower()
              if source.suffix.lower() in OPENERS else 'none', 'complete': False,
              'decoded_bytes': 0}
    digest = hashlib.sha256()
    try:
        if source.suffix.lower() in {'.xz', '.lzma', '.bz2'}:
            blocks = strict_members(source)
            for block in blocks:
                output.write(block)
                digest.update(block)
                result['decoded_bytes'] += len(block)
        else:
            with OPENERS.get(source.suffix.lower(), open)(source, 'rb') as stream:
                for block in iter(lambda: stream.read(BLOCK_BYTES), b''):
                    output.write(block)
                    digest.update(block)
                    result['decoded_bytes'] += len(block)
        output.flush()
        result['complete'] = True
    except Exception as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    result['decoded_sha256'] = digest.hexdigest()
    with receipt.open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('receipt', type=Path)
    args = parser.parse_args()
    result = stream_source(args.source, sys.stdout.buffer, args.receipt)
    return 0 if result['complete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
