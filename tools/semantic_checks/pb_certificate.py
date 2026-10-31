"""Independent sufficient certificate for OPB/WBO and their SMT exports.

The source parser follows PB24's integer polynomial semantics. Target terms
are normalized independently, using exact integers and x*x=x only after the
complete {0,1} domains have been matched. Equality of the resulting constraint
sets and signed cost polynomials proves pointwise correspondence, without a
SAT search. A matching independent whole-target SMT typecheck is a prerequisite;
this certificate establishes correspondence, not general SMT well-sortedness.
Unsupported encodings are inconclusive, never counterexamples.
The checked source spelling currently uses ASCII identifiers. Linear auxiliary
encodings use the separate unique-extension proof in pb_projected_certificate.
"""
from collections import Counter
from dataclasses import dataclass, field
import bz2
import gzip
import hashlib
import json
import lzma
from math import gcd
from pathlib import Path
import re


class CertificateError(ValueError):
    pass


def constant(value):
    return {(): value} if value else {}


def add(left, right, scale=1):
    result = left.copy()
    accumulate(result, right, scale)
    return result


def accumulate(result, right, scale=1):
    """Accumulate into an owned polynomial without copying each prefix sum."""
    for monomial, coefficient in right.items():
        value = result.get(monomial, 0) + scale * coefficient
        if value:
            result[monomial] = value
        else:
            result.pop(monomial, None)


def multiply(left, right):
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            # Every factor is either a checked binary variable or a Boolean
            # indicator. Thus repeated factors may be reduced idempotently.
            monomial = tuple(sorted(set(a).union(b)))
            value = result.get(monomial, 0) + x * y
            if value:
                result[monomial] = value
            else:
                result.pop(monomial, None)
    return result


def frozen(poly):
    return tuple(sorted(poly.items()))


TRUE, FALSE = ('bool', True), ('bool', False)


def relation(operator, left, right):
    poly = add(left, right, -1)
    if operator in ('<=', '<'):
        poly = {m: -c for m, c in poly.items()}
        operator = '>=' if operator == '<=' else '>'
    if operator == '>':
        poly = add(poly, constant(-1))
        operator = '>='
    if operator not in ('>=', '=', '!='):
        raise CertificateError(f'unsupported relation {operator}')
    if set(poly) <= {()}:
        value = poly.get((), 0)
        answer = value >= 0 if operator == '>=' else value == 0
        return ('bool', not answer if operator == '!=' else answer)
    divisor = 0
    for coefficient in poly.values():
        divisor = gcd(divisor, coefficient)
    if divisor > 1:
        poly = {m: c // divisor for m, c in poly.items()}
    if operator in ('=', '!=') and sorted(poly.items())[0][1] < 0:
        poly = {m: -c for m, c in poly.items()}
    return operator, frozen(poly)


def negate(value):
    if value[0] == 'bool':
        return ('bool', not value[1])
    if value[0] in ('=', '!='):
        return ('!=' if value[0] == '=' else '=', value[1])
    if value[0] == '>=':
        return relation('<', dict(value[1]), {})
    if value[0] == 'not':
        return value[1]
    return 'not', value


def conjunction(values):
    values = set(values)
    if FALSE in values:
        return FALSE
    values.discard(TRUE)
    if not values:
        return TRUE
    if len(values) == 1:
        return next(iter(values))
    return 'and', tuple(sorted(values, key=repr))


@dataclass
class Context:
    indicators: dict = field(default_factory=dict)
    public_variables: set = field(default_factory=set)

    def indicator(self, boolean):
        if boolean == TRUE:
            return constant(1)
        if boolean == FALSE:
            return {}
        # Exact tuple interning, not probabilistic digest equality.
        if boolean not in self.indicators:
            self.indicators[boolean] = len(self.indicators)
        return {(f'b:{self.indicators[boolean]}',): 1}


@dataclass
class SourceModel:
    variables: set = field(default_factory=set)
    hard: set = field(default_factory=set)
    soft: Counter = field(default_factory=Counter)
    objective: object = None
    top: object = None
    wbo: bool = False
    rows: int = 0


SOURCE_TOKEN = re.compile(r'\s*(>=|<=|!=|[≥≤≠=<>]|[+\-]?\d+|[+\-~\[\]:]|[A-Za-z_][A-Za-z_0-9]*)')
INTEGER = re.compile(r'[+\-]?\d+\Z')
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*\Z')


def source_tokens(statement):
    result, pos = [], 0
    while pos < len(statement):
        match = SOURCE_TOKEN.match(statement, pos)
        if match is None:
            if statement[pos:].strip():
                raise CertificateError(f'unsupported source spelling at {statement[pos:pos+60]!r}')
            break
        result.append(match.group(1))
        pos = match.end()
    return result


def integer(tokens, pos):
    if pos >= len(tokens):
        raise CertificateError('missing integer')
    token = tokens[pos]
    if token in ('+', '-'):
        if pos + 1 >= len(tokens) or not tokens[pos+1].isdigit():
            raise CertificateError('sign is not followed by a numeral')
        return int(token + tokens[pos+1]), pos + 2
    if not INTEGER.fullmatch(token):
        raise CertificateError(f'expected integer, got {token!r}')
    return int(token), pos + 1


def source_sum(tokens, model):
    result, pos = {}, 0
    while pos < len(tokens):
        coefficient, pos = integer(tokens, pos)
        term, count = constant(coefficient), 0
        while pos < len(tokens) and (tokens[pos] == '~' or IDENTIFIER.fullmatch(tokens[pos])):
            negative = tokens[pos] == '~'
            pos += negative
            if pos == len(tokens) or not IDENTIFIER.fullmatch(tokens[pos]):
                raise CertificateError('missing literal name')
            name = tokens[pos]
            model.variables.add(name)
            variable = {('v:' + name,): 1}
            literal = add(constant(1), variable, -1) if negative else variable
            term = multiply(term, literal)
            pos += 1
            count += 1
        if not count and coefficient:
            raise CertificateError('nonzero source term has no literal')
        accumulate(result, term)
    return result


def parse_source(stream, context):
    model, buffer, started = SourceModel(), '', False
    digest = hashlib.sha256()
    for raw in stream:
        digest.update(raw)
        line = raw.decode('utf-8')
        if line.lstrip().startswith('*'):
            continue
        buffer += line
        while ';' in buffer:
            statement, buffer = buffer.split(';', 1)
            tokens = source_tokens(statement)
            if not tokens:
                raise CertificateError('empty source statement')
            if tokens[:2] in (['min', ':'], ['max', ':'], ['soft', ':']):
                if started:
                    raise CertificateError('objective/header must precede all constraints')
                if tokens[0] == 'soft':
                    model.wbo = True
                    if len(tokens) > 2:
                        model.top, end = integer(tokens, 2)
                        if end != len(tokens) or model.top <= 0:
                            raise CertificateError('invalid finite WBO threshold')
                else:
                    poly = source_sum(tokens[2:], model)
                    model.objective = poly if tokens[0] == 'min' else {m: -c for m, c in poly.items()}
                started = True
                continue
            started = True
            weight = None
            if tokens[0] == '[':
                if not model.wbo:
                    raise CertificateError('soft row lacks WBO header')
                weight, end = integer(tokens, 1)
                if weight <= 0 or end >= len(tokens) or tokens[end] != ']':
                    raise CertificateError('invalid soft row weight')
                tokens = tokens[end+1:]
            comparisons = [i for i, t in enumerate(tokens) if t in ('>=', '<=', '!=', '=', '>', '<', '≥', '≤', '≠')]
            if len(comparisons) != 1:
                raise CertificateError('expected exactly one source comparator')
            split = comparisons[0]
            lhs = source_sum(tokens[:split], model)
            rhs, end = integer(tokens, split+1)
            if end != len(tokens):
                raise CertificateError('trailing source tokens')
            operator = {'≥': '>=', '≤': '<=', '≠': '!='}.get(tokens[split], tokens[split])
            row = relation(operator, lhs, constant(rhs))
            model.rows += 1
            if weight is None:
                model.hard.add(row)
            else:
                model.soft[row] += weight
    if buffer.strip():
        raise CertificateError('unterminated source statement')
    for name in model.variables:
        variable = {('v:' + name,): 1}
        model.hard.add(relation('>=', variable, {}))
        model.hard.add(relation('<=', variable, constant(1)))
    if model.wbo:
        cost = {}
        for row, weight in model.soft.items():
            accumulate(cost, add(constant(1), context.indicator(row), -1), weight)
        model.objective = cost
        # Positive weights make this bound provably vacuous only if top
        # exceeds the complete sum. Equality at the threshold is forbidden.
        if model.top is not None and model.top <= sum(model.soft.values()):
            model.hard.add(relation('<', cost, constant(model.top)))
    model.hard.discard(TRUE)
    return model, digest.hexdigest()


class TargetReader:
    def __init__(self, stream):
        self.stream, self.digest = stream, hashlib.sha256()

    def expressions(self):
        stack = []
        for raw in self.stream:
            self.digest.update(raw)
            text = raw.decode('utf-8').split(';', 1)[0]
            for token in re.findall(r'\(|\)|[^\s()]+', text):
                if token == '(':
                    stack.append([])
                elif token == ')':
                    if not stack:
                        raise CertificateError('unmatched target close parenthesis')
                    item = stack.pop()
                    if stack:
                        stack[-1].append(item)
                    else:
                        yield item
                elif stack:
                    stack[-1].append(token)
                else:
                    raise CertificateError('target token outside a command')
        if stack:
            raise CertificateError('unterminated target expression')


def raw_binary_bounds(expression, public):
    """Recognize unconditional domains without polynomial/idempotent rewrites.

    Using a normalized x*x<=1 to establish x<=1 would be circular: an Int
    target could also admit x=-1. Only the raw variable and literal bounds
    below can discharge the premise of our Boolean polynomial rewriting.
    """
    if not isinstance(expression, list) or not expression:
        return set()
    if expression[0] == 'and':
        result = set()
        for child in expression[1:]:
            result.update(raw_binary_bounds(child, public))
        return result
    if len(expression) != 3 or expression[0] not in ('>=', '<='):
        return set()
    operator, left, right = expression
    if isinstance(right, str) and right in public:
        left, right = right, left
        operator = '<=' if operator == '>=' else '>='
    if not isinstance(left, str) or left not in public or not isinstance(right, str):
        return set()
    expected = 0 if operator == '>=' else 1
    if right == str(expected) or re.fullmatch(str(expected) + r'\.0+', right):
        return {(left, expected)}
    return set()


def term(expression, declarations, context, env=None):
    env = {} if env is None else env
    if isinstance(expression, str):
        if expression in env:
            return env[expression]
        if expression in ('true', 'false'):
            return 'bool', expression == 'true'
        if re.fullmatch(r'\d+', expression):
            return constant(int(expression))
        if re.fullmatch(r'\d+\.0+', expression):
            # Some target printers promote integer-valued objectives to Real.
            # The strict-inequality normalization remains valid only because
            # these admitted decimals are exact mathematical integers.
            return constant(int(expression.split('.', 1)[0]))
        if expression in declarations:
            return {('v:' + expression,): 1}
        raise CertificateError(f'undeclared or unsupported target atom {expression!r}')
    if not expression:
        raise CertificateError('empty target application')
    op, *args = expression
    if op == 'let' and len(args) == 2:
        local = env.copy()
        names = set()
        for binding in args[0]:
            if len(binding) != 2 or not isinstance(binding[0], str) or binding[0] in names:
                raise CertificateError('malformed or duplicate lexical binding')
            names.add(binding[0])
            local[binding[0]] = term(binding[1], declarations, context, env)
        return term(args[1], declarations, context, local)
    values = [term(arg, declarations, context, env) for arg in args]
    if op == 'to_real' and len(values) == 1 and isinstance(values[0], dict):
        return values[0]
    if op in ('+', '-', '*'):
        if not values or any(not isinstance(x, dict) for x in values):
            raise CertificateError('invalid integer application')
        if op == '+':
            out = {}
            for value in values:
                accumulate(out, value)
            return out
        if op == '*':
            out = constant(1)
            for value in values:
                if any(out) and any(value) and any(
                    atom.startswith('v:') and atom[2:] not in context.public_variables
                    for monomial in tuple(out) + tuple(value) for atom in monomial
                ):
                    # Private cost coordinates need not be binary. Their
                    # encodings are linear, so never apply x*x=x to them.
                    raise CertificateError('nonlinear product of private coordinates')
                out = multiply(out, value)
            return out
        if len(values) == 1:
            return {m: -c for m, c in values[0].items()}
        out = values[0]
        for value in values[1:]:
            out = add(out, value, -1)
        return out
    if op in ('=', '>=', '<=', '>', '<') and len(values) == 2 and all(isinstance(x, dict) for x in values):
        return relation(op, *values)
    if op == '=' and len(values) == 2 and all(not isinstance(x, dict) for x in values):
        return 'iff', tuple(sorted(values, key=repr))
    if op == 'not' and len(values) == 1 and not isinstance(values[0], dict):
        return negate(values[0])
    if op == 'and' and values and all(not isinstance(x, dict) for x in values):
        return conjunction(values)
    if op == 'ite' and len(values) == 3 and not isinstance(values[0], dict) and all(isinstance(x, dict) for x in values[1:]):
        return add(values[2], multiply(context.indicator(values[0]), add(values[1], values[2], -1)))
    raise CertificateError(f'unsupported target operator/arity/sorts: {op}')


def hardened_wbo_matches(source, hard, objective, context):
    """Prove threshold-implied hard rows and cost on the feasible domain.

    All weights are positive. A row of weight >= top cannot be violated by
    an assignment whose cost is strictly below top. Making those rows hard
    and removing their zero contributions preserves the complete feasible
    relation and its pointwise cost; merely dropping the threshold does not.
    """
    if not source.wbo or source.top is None:
        return False
    mandatory = {row for row, weight in source.soft.items() if weight >= source.top}
    if not mandatory:
        return False
    expected_hard = set(source.hard)
    expected_hard.discard(relation('<', source.objective, constant(source.top)))
    expected_hard.update(mandatory)
    cost, total = {}, 0
    for row, weight in source.soft.items():
        if row in mandatory:
            continue
        total += weight
        accumulate(cost, add(constant(1), context.indicator(row), -1), weight)
    if source.top <= total:
        expected_hard.add(relation('<', cost, constant(source.top)))
    expected_hard.discard(TRUE)
    # An absent optimization command denotes the same constant-zero cost
    # when every soft row has been proved mandatory.
    actual_cost = {} if objective is None and not cost else objective
    return hard == expected_hard and actual_cost == cost


def verify_streams(source_stream, target_stream):
    context = Context()
    source, source_sha = parse_source(source_stream, context)
    context.public_variables = source.variables
    reader = TargetReader(target_stream)
    declarations, hard, soft, objective = set(), set(), {}, None
    established_domains = set()
    phase, saw_logic = 'declarations', False
    for command in reader.expressions():
        if not command:
            raise CertificateError('empty command')
        name = command[0]
        if phase == 'exit':
            raise CertificateError('command after exit')
        if name == 'set-logic' and command == ['set-logic', 'ALL'] and not saw_logic and not declarations and phase == 'declarations':
            saw_logic = True
        elif name == 'declare-fun' and len(command) == 4 and command[2:] == [[], 'Int'] and phase in ('declarations', 'body'):
            symbol = command[1]
            if not isinstance(symbol, str) or not re.fullmatch(r'[A-Za-z_!$][A-Za-z_0-9!$@.\-]*|\|[^|\s]+\|', symbol) or symbol in declarations:
                raise CertificateError('unsupported/duplicate target declaration')
            declarations.add(symbol)
        elif name in ('assert', 'assert-soft', 'minimize', 'maximize') and phase in ('declarations', 'body'):
            phase = 'body'
            if len(command) < 2:
                raise CertificateError('missing command argument')
            if name == 'assert' and len(command) == 2:
                established_domains.update(raw_binary_bounds(command[1], source.variables))
            value = term(command[1], declarations, context)
            if name == 'assert' and len(command) == 2 and not isinstance(value, dict):
                if value[0] == 'and':
                    hard.update(value[1])
                else:
                    hard.add(value)
            elif name == 'assert-soft' and len(command) == 4 and command[2] == ':weight' and isinstance(command[3], str) and command[3].isdigit() and int(command[3]) > 0 and not isinstance(value, dict):
                accumulate(soft, add(constant(1), context.indicator(value), -1), int(command[3]))
            elif name in ('minimize', 'maximize') and len(command) == 2 and isinstance(value, dict) and objective is None:
                objective = value if name == 'minimize' else {m: -c for m, c in value.items()}
            else:
                raise CertificateError(f'invalid target command {name}')
        elif command == ['check-sat'] and phase in ('declarations', 'body'):
            phase = 'checked'
        elif command == ['exit']:
            phase = 'exit'
        else:
            raise CertificateError(f'unsupported or misplaced target command {name}')
    if soft:
        if objective is not None:
            raise CertificateError('mixed soft and explicit objective requires priority proof')
        objective = soft
    elif source.wbo and objective is None and not source.soft:
        objective = {}
    hard.discard(TRUE)
    required_domains = {(name, bound) for name in source.variables for bound in (0, 1)}
    if established_domains != required_domains:
        raise CertificateError('raw target Boolean domains not established independently of polynomial rewrites')
    if declarations != source.variables:
        if not source.wbo or soft:
            raise CertificateError(f'source/target declarations differ: {len(source.variables)} / {len(declarations)}; auxiliary projection may be required')
        try:
            from .pb_projected_certificate import certify_projected_wbo
        except ImportError:
            from pb_projected_certificate import certify_projected_wbo
        projection = certify_projected_wbo(source, declarations, hard, objective, context)
        return dict(status='verified', method='linear WBO unique-extension certificate',
                    source_sha256=source_sha, target_sha256=reader.digest.hexdigest(),
                    variables=len(source.variables), source_rows=source.rows,
                    solver_search_performed=False, complete_source=True, complete_target=True,
                    objective_verified=True, projection=projection,
                    requires_matching_independent_whole_target_typecheck=True,
                    raw_public_domains_checked=True)
    hardened = hardened_wbo_matches(source, hard, objective, context)
    if hard != source.hard and not hardened:
        raise CertificateError(f'hard relation correspondence unestablished: missing {len(source.hard-hard)}, extra {len(hard-source.hard)}')
    if objective != source.objective and not hardened:
        raise CertificateError('signed pointwise cost correspondence unestablished')
    return dict(status='verified', method='exact Boolean-domain polynomial and signed-cost correspondence',
                source_sha256=source_sha, target_sha256=reader.digest.hexdigest(),
                variables=len(declarations), source_rows=source.rows, target_distinct_hard=len(hard),
                source_soft_distinct=len(source.soft), objective_verified=objective is not None or hardened,
                threshold_implied_hardening=hardened,
                cost_correspondence_domain='complete feasible source relation',
                solver_search_performed=False, complete_source=True, complete_target=True,
                requires_matching_independent_whole_target_typecheck=True,
                raw_public_domains_checked=True)


def open_source(path):
    path = Path(path)
    with path.open('rb') as stream:
        magic = stream.read(6)
    opener = lzma.open if magic.startswith(b'\xfd7zXZ') else gzip.open if magic.startswith(b'\x1f\x8b') else bz2.open if magic.startswith(b'BZh') else open
    return opener(path, 'rb')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('source')
    parser.add_argument('target')
    args = parser.parse_args()
    with open_source(args.source) as source, open_source(args.target) as target:
        print(json.dumps(verify_streams(source, target), sort_keys=True))
