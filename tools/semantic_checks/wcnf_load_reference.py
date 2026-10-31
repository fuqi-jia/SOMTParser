"""Whole-module typecheck bridge for the emitted WCNF SMT subset.

No solver is called and the bridged module is never used for relation/cost
checking. Hard assertions and declarations remain byte-for-byte commands.
Each soft Boolean term is parsed once in a local let-bound tautology. Exact
weights and command order are validated and digested; complete source/target
cost equivalence remains a separate certificate on the original byte stream.
"""
import hashlib
from tools.validate_packed_smt_stream import HashReader, Rejected, command_head, commands


def need(condition, message):
    if not condition:
        raise Rejected(message)


def _token(token):
    kind, raw = token
    if kind == 'quoted':
        return b'|' + raw + b'|'
    if kind == 'string':
        return b'"' + raw + b'"'
    return raw


def _term(tokens):
    token = next(tokens, None)
    need(token is not None and token != ('paren', b')'), 'missing term')
    parts = [_token(token)]
    depth = int(token == ('paren', b'('))
    while depth:
        token = next(tokens, None)
        need(token is not None, 'truncated term')
        depth += int(token == ('paren', b'(')) - int(token == ('paren', b')'))
        parts.append(_token(token))
    return b' '.join(parts)


def bridge(source, destination):
    reader = HashReader(source)
    output_hash, weights_hash = hashlib.sha256(), hashlib.sha256()
    count = dict(commands=0, declarations=0, hard_assertions=0, soft_assertions=0)
    output_bytes = 0
    phase, logic, queried, exited = 'prefix', False, False, False
    for command in commands(reader, max_command_bytes=float('inf')):
        need(not exited, 'content after exit')
        head, tokens = command_head(command)
        emitted = command.raw
        if head == 'set-logic':
            need(not logic and phase == 'prefix' and count['declarations'] == 0,
                 'duplicate or late logic')
            need(list(tokens) == [('atom', b'ALL'), ('paren', b')')], 'unsupported logic')
            logic = True
        elif head in ('declare-const', 'declare-fun'):
            need(phase == 'prefix', 'late declaration')
            row = list(tokens)
            need(row and row[0][0] in ('atom', 'quoted'), 'invalid declaration name')
            suffix = [('atom', b'Bool'), ('paren', b')')]
            if head == 'declare-fun':
                suffix = [('paren', b'('), ('paren', b')')] + suffix
            need(row[1:] == suffix, 'WCNF requires nullary Boolean declarations')
            count['declarations'] += 1
        elif head == 'assert':
            need(phase != 'queries', 'assertion after query')
            phase = 'body'
            _term(tokens)
            need(list(tokens) == [('paren', b')')], 'assert arity')
            count['hard_assertions'] += 1
        elif head == 'assert-soft':
            need(phase != 'queries', 'soft assertion after query')
            phase = 'body'
            term = _term(tokens)
            attributes = list(tokens)
            need(len(attributes) == 3 and attributes[0] == ('atom', b':weight')
                 and attributes[1][0] == 'atom' and attributes[2] == ('paren', b')'),
                 'unsupported soft attributes, group, or arity')
            weight = attributes[1][1]
            need(weight and all(48 <= byte <= 57 for byte in weight)
                 and any(byte != 48 for byte in weight), 'positive integer weight required')
            weights_hash.update(str(command.index).encode() + b':' + weight + b'\n')
            # SMT let bindings are simultaneous/nonrecursive: original term is
            # evaluated in the original environment, even if it uses this name.
            emitted = (b'(assert (let ((|somt.soft.check| ' + term
                       + b')) (or |somt.soft.check| (not |somt.soft.check|))))')
            count['soft_assertions'] += 1
        elif head in ('check-sat', 'exit'):
            need(list(tokens) == [('paren', b')')], 'query arity')
            phase = 'queries'
            if head == 'check-sat':
                need(not queried, 'duplicate check-sat')
                queried = True
            else:
                need(queried, 'exit without check-sat')
                exited = True
        else:
            raise Rejected('unsupported WCNF target command: ' + head)
        emitted += b'\n'
        destination.write(emitted)
        output_hash.update(emitted)
        output_bytes += len(emitted)
        count['commands'] += 1
    need(reader.complete and queried and exited, 'incomplete target/query tail')
    destination.flush()
    return dict(**count, original_sha256=reader.hash.hexdigest(),
                original_bytes=reader.bytes, original_eof=True,
                bridged_sha256=output_hash.hexdigest(), bridged_bytes=output_bytes,
                ordered_soft_weights_sha256=weights_hash.hexdigest(),
                objective_encoding='original weighted Boolean soft assertions',
                parser_scope='CVC5 bridged whole-module typecheck',
                unchanged_original_script_parse=False, solver_search=False,
                relation_and_cost_check='requires exact original-stream certificate')
