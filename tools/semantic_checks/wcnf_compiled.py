"""Feed complete compressed inputs to the independent native WCNF certificate.

The native binary compares exact keys; SHA-256 binds the complete input streams
and executable to this receipt. This is source/target semantic checking, not
whole-module loading, SAT solving, or an optimization-result comparison.
"""
from pathlib import Path
import argparse
import bz2
import gzip
import hashlib
import json
import lzma
import os
import subprocess
import threading


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def open_input(path):
    with Path(path).open('rb') as stream:
        magic = stream.read(6)
    opener = lzma.open if magic.startswith(b'\xfd7zXZ') else gzip.open if magic.startswith(b'\x1f\x8b') else bz2.open if magic.startswith(b'BZh') else open
    return opener(path, 'rb')


def verify_files(source_path, target_path, executable):
    executable = Path(executable).resolve()
    binary_sha = sha(executable)
    pipes = [os.pipe(), os.pipe()]
    process = subprocess.Popen([str(executable), *(f'/proc/self/fd/{r}' for r, _ in pipes)],
                               pass_fds=[r for r, _ in pipes], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    for read_fd, _ in pipes:
        os.close(read_fd)
    receipts = [{}, {}]
    def feed(index, path, fd):
        digest = hashlib.sha256()
        size = 0
        try:
            with os.fdopen(fd, 'wb') as sink, open_input(path) as source:
                while block := source.read(1024 * 1024):
                    sink.write(block)
                    digest.update(block)
                    size += len(block)
                sink.flush()
            receipts[index].update(sha256=digest.hexdigest(), bytes=size, complete_eof=True)
        except BaseException as error:
            receipts[index].update(sha256=digest.hexdigest(), bytes=size,
                                   complete_eof=False, error=repr(error))
    threads = [threading.Thread(target=feed, args=(i, path, pipes[i][1]))
               for i, path in enumerate([source_path, target_path])]
    for thread in threads:
        thread.start()
    stdout, stderr = process.communicate()
    for thread in threads:
        thread.join()
    result = json.loads(stdout) if stdout else dict(status='unverified', error='native checker produced no JSON')
    result.update(native_sha256=binary_sha, native_path=str(executable), returncode=process.returncode,
                  stderr=stderr.decode(errors='replace'), source_stream=receipts[0],
                  target_stream=receipts[1], whole_module_loading_performed=False,
                  solver_search_performed=False)
    result['passed'] = (process.returncode == 0 and result.get('status') == 'verified'
                        and all(r.get('complete_eof') is True for r in receipts)
                        and sha(executable) == binary_sha)
    if not result['passed']:
        result['status'] = 'unverified'
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source')
    parser.add_argument('target')
    parser.add_argument('--executable', required=True)
    args = parser.parse_args()
    result = verify_files(args.source, args.target, args.executable)
    print(json.dumps(result))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
