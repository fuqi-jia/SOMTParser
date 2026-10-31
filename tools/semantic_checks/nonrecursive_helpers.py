"""Normalize only provably nonrecursive SMT-LIB recursive declarations.

The whole original module must first pass solver parsing. This operation changes
only command-head bytes, retaining every parameter, body, assertion and objective.
The sufficient nonrecursion check follows the qualified XCSP target reader.
"""
import hashlib
import io
import re
from tools import validate_packed_smt_stream as scanner


def normalize(data):
    names = set()
    edits = []
    for command in scanner.commands(io.BytesIO(data), max_command_bytes=float('inf')):
        head, stream = scanner.command_head(command)
        if head in ('push', 'pop', 'reset', 'reset-assertions', 'define-funs-rec'):
            raise ValueError('stateful or mutually recursive module is unsupported')
        if head not in ('declare-const', 'declare-fun', 'define-fun', 'define-fun-rec'):
            continue
        tokens = list(stream)
        if not tokens or tokens[0][0] not in ('atom', 'quoted'):
            raise ValueError('missing declaration identifier')
        name = tokens[0][1]
        if name in names:
            raise ValueError('declaration identity collision')
        names.add(name)
        if head != 'define-fun-rec':
            continue
        if any(kind in ('atom', 'quoted') and value == name for kind, value in tokens[1:]):
            raise ValueError('recursive or shadowed helper is unsupported: ' + name.decode())
        match = re.match(br'^\(\s*(define-fun-rec)(?=\s)', command.raw)
        if not match:
            raise ValueError('unsupported recursive declaration command boundary')
        start = command.start + match.start(1)
        end = command.start + match.end(1)
        if data[start:end] != b'define-fun-rec':
            raise ValueError('scanner byte boundary differs')
        edits.append(dict(name=name.decode(), start=start, end=end,
                          command_sha256=hashlib.sha256(command.raw).hexdigest()))
    result = data
    for edit in reversed(edits):
        result = result[:edit['start']] + b'define-fun' + result[edit['end']:]
    return result, dict(method='nonrecursive-declaration-head-only-v1',
                        input_sha256=hashlib.sha256(data).hexdigest(),
                        output_sha256=hashlib.sha256(result).hexdigest(), edits=edits)
