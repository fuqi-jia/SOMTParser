"""Retain closed nonrecursive helper definitions without eager macro expansion.

A helper is eligible only when its complete definition parses in a fresh SMT
scope containing no globals or other helpers. Its integer/Boolean parameters
are therefore its only possible free inputs. Every helper receives a fresh
identifier per import, including all binding occurrences that shadow its name.
Non-closed helpers retain the existing macro expansion path.
"""
from itertools import count
import hashlib
import io
import uuid
import z3
from tools import validate_packed_smt_stream as scanner
from .nonrecursive_helpers import normalize


_fresh_serial = count()

def _render(tokens, renames=None):
    renames = renames or {}
    parts = []
    for kind, value in tokens:
        if kind in ('atom', 'quoted') and value in renames:
            parts.append(renames[value])
        elif kind == 'quoted':
            parts.append(b'|' + value + b'|')
        elif kind == 'string':
            parts.append(b'"' + value + b'"')
        else:
            parts.append(value)
    return b' '.join(parts)


def _closed_definition(tokens):
    """Check the complete body using SMT lexical scoping, including let binders."""
    # Full command tokens: ( define-fun-rec name ( (parameter Sort) ... ) Sort body )
    if len(tokens) < 9 or tokens[3] != ('paren', b'('):
        return False
    index, arguments = 4, []
    while index < len(tokens) and tokens[index] == ('paren', b'('):
        entry = tokens[index:index + 4]
        if (len(entry) != 4 or entry[1][0] not in ('atom', 'quoted')
                or entry[2] not in (('atom', b'Int'), ('atom', b'Bool'))
                or entry[3] != ('paren', b')')):
            return False
        arguments.append(b'0' if entry[2][1] == b'Int' else b'false')
        index += 4
    if (not arguments or tokens[index:index + 1] != [('paren', b')')]
            or tokens[index + 1:index + 2] not in ([('atom', b'Int')], [('atom', b'Bool')])):
        return False
    definition = list(tokens)
    definition[1] = ('atom', b'define-fun')
    name = _render([tokens[2]])
    call = b'(' + name + b' ' + b' '.join(arguments) + b')'
    module = _render(definition) + b'\n(assert (= ' + call + b' ' + call + b'))'
    try:
        # Unbound globals, declarations, and earlier helper references cannot
        # enter this isolated scope. An enclosing let follows normal SMT rules.
        z3.parse_smt2_string(module.decode(), ctx=z3.Context())
    except z3.Z3Exception:
        return False
    return True


def retain_closed_helpers(module):
    """Return the whole equivalent module and exact helper transformation pins."""
    # This retains the existing duplicate-identity and nonrecursion checks.
    expanded, expansion = normalize(module)
    commands = list(scanner.commands(io.BytesIO(module), max_command_bytes=float('inf')))
    token_rows = [list(scanner.tokens(command.raw)) for command in commands]
    used = {value for row in token_rows for kind, value in row if kind in ('atom', 'quoted')}
    chosen = {}
    for command, tokens in zip(commands, token_rows):
        if tokens[1] == ('atom', b'define-fun-rec') and _closed_definition(tokens):
            name = tokens[2][1]
            # The serial prevents reusing a generated name even if UUID repeats.
            fresh = ('__somt_oracle_closed_' + uuid.uuid4().hex + '_' + str(next(_fresh_serial))).encode()
            while fresh in used:
                fresh = ('__somt_oracle_closed_' + uuid.uuid4().hex + '_' + str(next(_fresh_serial))).encode()
            used.add(fresh)
            chosen[name] = dict(fresh=fresh, command_sha256=hashlib.sha256(command.raw).hexdigest())
    if not chosen:
        return expanded, dict(method='closed-helper-sharing-v1', shared=[], nonrecursion_check=expansion, expanded_helpers=[row['name'] for row in expansion['edits']])
    renames = {name: row['fresh'] for name, row in chosen.items()}
    output = []
    for tokens in token_rows:
        tokens = list(tokens)
        if tokens[1] == ('atom', b'define-fun-rec') and tokens[2][1] not in chosen:
            tokens[1] = ('atom', b'define-fun')
        output.append(_render(tokens, renames))
    result = b'\n'.join(output)
    return result, dict(method='closed-helper-sharing-v1', input_sha256=hashlib.sha256(module).hexdigest(),
                        output_sha256=hashlib.sha256(result).hexdigest(),
                        shared=[dict(original=name.decode(), fresh=row['fresh'].decode(),
                                     command_sha256=row['command_sha256'])
                                for name, row in chosen.items()], nonrecursion_check=expansion,
                        expanded_helpers=[row['name'] for row in expansion['edits'] if row['name'].encode() not in chosen])
