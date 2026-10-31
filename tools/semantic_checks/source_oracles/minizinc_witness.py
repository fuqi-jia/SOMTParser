"""Exact public MiniZinc assignments for independent solver concordance.

Output annotations and witness constraints never remove original model text.
No FlatZinc existential relation is built for these finite observations.
"""
from decimal import Decimal
from fractions import Fraction
from itertools import product
import json
import re
import z3
from types import SimpleNamespace

from .ozn_observations import Program, split, lex


def require(condition, message):
    if not condition:
        raise ValueError(message)


def typed_number(value):
    require(type(value) in (int, Decimal), 'exact JSON numeric value required')
    if type(value) is int:
        return {'type': 'int', 'value': str(value)}
    require(value.is_finite(), 'non-finite source number')
    value = Fraction(value)
    return {'type': 'real', 'numerator': str(value.numerator), 'denominator': str(value.denominator)}


def typed_value(value, kind, enums=None, source_enum=None):
    if kind == ['bool']:
        require(type(value) is bool, 'source Boolean required')
        return {'type': 'bool', 'value': value}
    if kind == ['int']:
        if isinstance(value, dict):
            require(source_enum in (enums or {}), 'enum type not established by source declaration')
            table = enums[source_enum]
            serialized = json.dumps(value, sort_keys=True)
            matches = [i + 1 for i, label in enumerate(table)
                       if json.dumps(label, sort_keys=True) == serialized]
            require(len(matches) == 1, 'enum value absent or duplicated in exact official/source catalog')
            value = matches[0]
        require(type(value) is int, 'source integer required')
        return typed_number(value)
    if kind == ['float']:
        if type(value) is int:
            value = Decimal(value)
        require(type(value) is Decimal, 'exact decimal source real required')
        return typed_number(value)
    if kind == ['set', 'of', 'int']:
        require(isinstance(value, dict) and set(value) == {'set'}, 'source finite-set JSON required')
        elements = set()
        for entry in value['set']:
            if isinstance(entry, list):
                require(len(entry) == 2 and all(type(x) is int for x in entry) and entry[0] <= entry[1], 'finite-set range')
                elements.update(range(entry[0], entry[1] + 1))
            elif isinstance(entry, dict):
                elements.add(int(typed_value(entry, ['int'], enums, source_enum)['value']))
            else:
                require(type(entry) is int, 'finite-set element')
                elements.add(entry)
        return {'type': 'set-int', 'elements': [str(x) for x in sorted(elements)]}
    raise ValueError('unsupported exact source value kind ' + repr(kind))


def solution_stream(lines, method):
    last = None
    statuses = []
    errors = []
    count = 0
    for line in lines:
        event = json.loads(line, parse_float=Decimal)
        if event.get('type') == 'solution':
            require(isinstance(event.get('output', {}).get('json'), dict), 'missing full JSON solution')
            last = event['output']['json']
            count += 1
        elif event.get('type') == 'status':
            statuses.append(event['status'])
        elif event.get('type') == 'error':
            errors.append(event)
    require(method in ('satisfy', 'minimize', 'maximize'), 'source solve method')
    if errors or 'ERROR' in statuses:
        return {'status': 'error', 'errors': errors, 'statuses': statuses}
    if 'UNSATISFIABLE' in statuses:
        require(last is None, 'UNSAT stream also contains a solution')
        return {'status': 'unsat', 'optimal': False, 'solutions': count, 'statuses': statuses}
    if last is None:
        return {'status': 'unknown', 'optimal': False, 'statuses': statuses}
    objectives = [] if method == 'satisfy' else [typed_number(last['_objective'])]
    return {'status': 'sat', 'optimal': method == 'satisfy' or statuses[-1:] == ['OPTIMAL_SOLUTION'],
            'solution': last, 'original_objective_values': objectives,
            'solutions': count, 'statuses': statuses}


def source_method(source):
    statements = split(lex(source), ';')
    solves = [s for s in statements if s[:1] == ['solve']]
    require(len(solves) == 1, 'exactly one original solve item required')
    depth = 0
    found = []
    for token in solves[0][1:]:
        if token in ('(', '[', '{'):
            depth += 1
        elif token in (')', ']', '}'):
            depth -= 1
        elif depth == 0 and token in ('satisfy', 'minimize', 'maximize'):
            found.append(token)
    require(len(found) == 1, 'source solve direction missing or ambiguous')
    return found[0]


def observation_schema(ozn, declarations, source_bytes):
    program = Program(ozn, SimpleNamespace(variables={}, arrays={}, constraints=[], integer_domains={}))
    enums = {}
    for name, (head, rhs) in program.declarations.items():
        match = re.fullmatch(r'_enum_to_string_0_(.+)', name)
        if match and rhs is not None:
            labels = json.loads(''.join(rhs))
            require(isinstance(labels, list) and all(isinstance(x, str) for x in labels), 'official enum string table')
            require(len(set(labels)) == len(labels), 'duplicate official enum labels')
            enums[match.group(1)] = [{'e': label} for label in labels]
    definitions = {}
    for statement in split(lex(source_bytes.decode()), ';'):
        if statement[:1] == ['enum'] and len(statement) > 3 and statement[2] == '=':
            definitions[statement[1]] = statement[3:]
    known_enums = set(enums) | set(definitions)
    active = set()
    resolved = set()

    def catalog(name):
        require(name not in active, 'cyclic enum catalog')
        if name in resolved or name not in definitions:
            require(name in enums, 'missing official enum labels ' + name)
            return enums[name]
        active.add(name)
        values = []
        for component_index, component in enumerate(split(definitions[name], '++')):
            if component[:1] == ['{'] and component[-1:] == ['}']:
                for label in split(component[1:-1], ','):
                    if not label:
                        continue
                    require(len(label) == 1 and re.fullmatch(r'[A-Za-z_]\w*', label[0]), 'enum literal label')
                    values.append({'e': label[0]})
            else:
                require(len(component) >= 4 and component[1] == '(' and component[-1] == ')'
                        and re.fullmatch(r'[A-Za-z_]\w*', component[0]), 'finite enum constructor')
                argument = component[2:-1]
                carrier = '_constrId_' + str(component_index) + '_' + name
                # OZN may fold away a source parameter used by the constructor.
                # Its evaluated carrier and ordinal offset remain authoritative.
                domain = (program.name(carrier, {}) if carrier in program.declarations
                          else program.expression(argument, {}))
                require(isinstance(domain, frozenset) and all(type(x) is int for x in domain), 'constructor integer carrier')
                if len(argument) == 1 and argument[0] in known_enums:
                    members = catalog(argument[0])
                    require(sorted(domain) == list(range(1, len(members) + 1)), 'constructor enum ordinal domain')
                else:
                    members = sorted(domain)
                offset_name = '_constrMin_' + str(component_index) + '_' + name
                if offset_name in program.declarations:
                    offset = program.name(offset_name, {})
                    if z3.is_int_value(offset):
                        offset = offset.as_long()
                    require(type(offset) is int and [x + offset for x in sorted(domain)]
                            == list(range(len(values) + 1, len(values) + len(members) + 1)),
                            'official constructor ordinal offset differs')
                values.extend({'c': component[0], 'e': item} for item in members)
        if name in program.declarations:
            domain = program.name(name, {})
            require(isinstance(domain, frozenset) and sorted(domain) == list(range(1, len(values) + 1)), 'source enum catalog and official domain differ')
        else:
            require(name in enums and enums[name] == values, 'source enum catalog lacks an exact official string table')
        require(len({json.dumps(v, sort_keys=True) for v in values}) == len(values), 'ambiguous enum constructors')
        enums[name] = values
        active.remove(name)
        resolved.add(name)
        return values

    rows = []
    for declaration in declarations:
        name = declaration['name']
        require(name in program.declarations, 'declared observation missing from official OZN: ' + name)
        head, rhs = program.declarations[name]
        original = source_bytes[declaration['statement_start']:declaration['name_start']].decode()
        type_tokens = lex(original)
        var_position = max((i for i, t in enumerate(type_tokens) if t == 'var'), default=-1)
        value_kind = type_tokens[var_position + 1:]
        if value_kind[-1:] == [':']:
            value_kind = value_kind[:-1]
        source_enum = (value_kind[0] if len(value_kind) == 1 and value_kind[0] in known_enums
                       else value_kind[2] if value_kind[:2] == ['set', 'of'] and len(value_kind) == 3 and value_kind[2] in known_enums
                       else None)
        if source_enum is not None:
            catalog(source_enum)
        if head[:1] == ['array']:
            end = head.index(']')
            kind = head[end + 2:]
            dim_tokens = split(head[2:end], ',')
            dimensions = []
            for expression in dim_tokens:
                if expression == ['int']:
                    # Infer the exact extent from an explicit official arrayNd
                    # constructor only; never infer it from an arbitrary target.
                    require(rhs is not None and re.fullmatch(r'array[1-6]d', rhs[0]) and rhs[1] == '(', 'unresolved official array extent')
                    args = split(rhs[2:-1], ',')
                    require(len(args) == len(dim_tokens) + 1, 'array constructor rank differs')
                    expression = args[len(dimensions)]
                value = program.expression(expression, {})
                require(isinstance(value, frozenset) and all(type(x) is int for x in value), 'finite original array index set')
                dimensions.append(sorted(value))
            index_enums = [t[0] if len(t) == 1 and t[0] in known_enums else None for t in dim_tokens]
            for enum_name in index_enums:
                if enum_name is not None:
                    catalog(enum_name)
        else:
            kind = head
            dimensions = None
            index_enums = None
        rows.append({'name': name, 'kind': kind, 'dimensions': dimensions,
                     'source_enum': source_enum, 'index_enums': index_enums})
    return {'schema': 'minizinc-exact-public-observations-v1', 'observables': rows, 'enum_tables': enums}


def flatten_values(value, dimensions):
    if not dimensions:
        return [value]
    require(isinstance(value, list) and len(value) == len(dimensions[0]), 'source JSON array extent mismatch')
    return [cell for child in value for cell in flatten_values(child, dimensions[1:])]


def project_solution(schema, solution, *, flatten_multidimensional_arrays):
    projection = []
    witness = {}
    for row in schema['observables']:
        name = row['name']
        require(name in solution, 'source solution omits observation ' + name)
        dimensions = row['dimensions']
        coordinates = list(product(*dimensions)) if dimensions is not None else [()]
        values = flatten_values(solution[name], dimensions or [])
        require(len(coordinates) == len(values), 'source coordinate/value cardinality mismatch')
        for offset, (coords, value) in enumerate(zip(coordinates, values)):
            identity = name + ('[' + ','.join(map(str, coords)) + ']' if dimensions is not None else '')
            if dimensions is None:
                indices = []
            elif len(dimensions) == 1:
                indices = list(coords)
            else:
                require(flatten_multidimensional_arrays, 'native multidimensional layout contract absent')
                indices = [offset]
            require(identity not in witness, 'duplicate public coordinate')
            projection.append({'id': identity, 'symbol': name, 'indices': indices,
                               'source_indices': list(coords), 'source_name': name})
            witness[identity] = typed_value(value, row['kind'], schema['enum_tables'], row['source_enum'])
    return projection, witness


def mzn_literal(value, enum=None):
    kind = value['type']
    if kind == 'int':
        n = int(value['value'])
        require(str(n) == value['value'], 'noncanonical integer')
        return 'to_enum(' + enum + ',' + str(n) + ')' if enum else str(n)
    if kind == 'bool':
        require(type(value['value']) is bool, 'Boolean witness value')
        return 'true' if value['value'] else 'false'
    if kind == 'real':
        n, d = int(value['numerator']), int(value['denominator'])
        require(d > 0, 'positive rational denominator required')
        return '(' + str(n) + '.0 / ' + str(d) + '.0)'
    if kind == 'set-int':
        return '{' + ','.join(mzn_literal({'type': 'int', 'value': x}, enum) for x in value['elements']) + '}'
    raise ValueError('unsupported witness type')


def witness_constraints(schema, projection, witness):
    require(set(witness) == {row['id'] for row in projection}, 'complete reverse witness coverage required')
    by_name = {r['name']: r for r in schema['observables']}
    result = []
    for cell in projection:
        row = by_name[cell['source_name']]
        term = cell['source_name']
        if row['dimensions'] is not None:
            require(len(cell['source_indices']) == len(row['dimensions']), 'original source rank')
            indices = [mzn_literal({'type': 'int', 'value': str(i)}, enum)
                       for i, enum in zip(cell['source_indices'], row['index_enums'])]
            term += '[' + ','.join(indices) + ']'
        result.append('constraint ' + term + ' = ' + mzn_literal(witness[cell['id']], row['source_enum']) + ';')
    return '\n'.join(result) + '\n'


def projection_schema(schema, *, flatten_multidimensional_arrays):
    result = []
    for row in schema['observables']:
        dims = row['dimensions']
        coords = product(*dims) if dims is not None else [()]
        for offset, indices in enumerate(coords):
            identity = row['name'] + ('[' + ','.join(map(str, indices)) + ']' if dims is not None else '')
            if dims is None:
                target = []
            elif len(dims) == 1:
                target = list(indices)
            else:
                require(flatten_multidimensional_arrays, 'native multidimensional layout contract absent')
                target = [offset]
            result.append({'id': identity, 'symbol': row['name'], 'indices': target,
                           'source_name': row['name'], 'source_indices': list(indices)})
    require(len({row['id'] for row in result}) == len(result), 'duplicate projected coordinate')
    return result
