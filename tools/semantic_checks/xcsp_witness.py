"""Complete XCSP integer witness exchange with the official Java checker."""
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET
from xml.parsers import expat


def declaration_sections(xml):
    """Parse all XML for well-formedness while retaining only declaration metadata."""
    builder = ET.TreeBuilder()
    parser = expat.ParserCreate()
    depth, retained_depth = 0, 0

    def start(name, attributes):
        nonlocal depth, retained_depth
        depth += 1
        if depth == 1:
            builder.start(name, attributes)
        elif depth == 2 and name in ('variables', 'objectives'):
            retained_depth = depth
            builder.start(name, attributes)
        elif retained_depth:
            builder.start(name, attributes)

    def end(name):
        nonlocal depth, retained_depth
        if retained_depth or depth == 1:
            builder.end(name)
        if retained_depth == depth:
            retained_depth = 0
        depth -= 1

    def data(text):
        if retained_depth:
            builder.data(text)

    parser.StartElementHandler = start
    parser.EndElementHandler = end
    parser.CharacterDataHandler = data
    # Chunk input so Expat never buffers the full constraint section as one token.
    for offset in range(0, len(xml), 65536):
        parser.Parse(xml[offset:offset + 65536], False)
    parser.Parse(b'' if isinstance(xml, bytes) else '', True)
    return builder.close()


class CoordinateNames(list):
    """Preserve selector order with constant-time mixed-domain membership."""
    def __contains__(self, value):
        if not hasattr(self, '_membership'):
            self._membership = frozenset(self)
        return value in self._membership


def declarations(xml):
    from tools.semantic_checks.source_oracles.xcsp_source import Reader
    root = declaration_sections(xml)
    if root.tag != 'instance' or root.get('type') not in ('CSP', 'COP'):
        raise ValueError('expected an original XCSP CSP/COP instance')
    class CoordinateReader(Reader):
        def selectors(self, token, declared=True):
            return CoordinateNames(super().selectors(token, declared))

        def declare(self, name, domain):
            # Coordinate exchange needs the original names/domains only.
            # All source constraints are checked by the independent Java checker.
            if name in self.variables or name in self.arrays:
                raise ValueError('duplicate source identity ' + name)
            self.variables[name] = None
            self.domains[name] = domain
    reader = CoordinateReader(reference_profile='official-java-cpp-open-default')
    reader.variables_xml(root.find('variables'))
    directions = []
    objectives = root.find('objectives')
    if objectives is not None:
        if objectives.get('combination', 'lexico') != 'lexico':
            raise ValueError('nonlexicographic objectives are unsupported')
        directions = [objective.tag for objective in objectives]
        if any(direction not in ('minimize', 'maximize') for direction in directions):
            raise ValueError('unknown objective direction')
    return reader, directions


def typed(values):
    return {name: {'type': 'int', 'value': str(value)} for name, value in values.items()}


def exact_values(witness, reader):
    if set(witness) != set(reader.variables):
        raise ValueError('incomplete or extra source coordinates')
    values = {}
    for name, row in witness.items():
        if row.get('type') != 'int' or not re.fullmatch(r'[+-]?\d+', str(row.get('value'))):
            raise ValueError('XCSP source coordinates must be exact integers')
        value = int(row['value'])
        if not any(lo <= value <= hi for lo, hi in reader.domains[name]):
            raise ValueError('source coordinate outside its original domain: ' + name)
        values[name] = value
    return values


def parse_ace_output(text, reader, directions):
    statuses = re.findall(r'^s\s+(SATISFIABLE|UNSATISFIABLE|OPTIMUM FOUND|UNKNOWN)\s*$', text, re.M)
    if not statuses:
        raise ValueError('ACE produced no recognized final status')
    status = statuses[-1]
    if re.search(r'^!\s*ERROR\b', text, re.M):
        return dict(status='error', optimal=False, witness=None, directions=directions,
                    reason='original solver reported an internal error', solver_error_reported=True)
    if status == 'UNKNOWN':
        return dict(status='unknown', optimal=False, witness=None, directions=directions,
                    reason='original solver reported UNKNOWN')
    if status == 'UNSATISFIABLE':
        return dict(status='unsat', optimal=False, witness=None, directions=directions)
    if directions and status != 'OPTIMUM FOUND':
        return dict(status='unknown', optimal=False, witness=None, directions=directions,
                    reason='original optimization not proved complete')
    content = '\n'.join(line[2:] for line in text.splitlines() if line.startswith('v '))
    candidates = re.findall(r'<instantiation\b[^>]*>.*?</instantiation>', content, re.S)
    if not candidates:
        raise ValueError('satisfiable ACE result lacks a complete instantiation')
    root = ET.fromstring(candidates[-1])
    listed = (root.findtext('list') or '').split()
    names = []
    if not listed:
        names = list(reader.variables)
    for token in listed:
        if token in reader.variables:
            names.append(token)
        elif '[' in token:
            names.extend(reader.selectors(token, declared=False))
        else:
            raise ValueError('unknown source solution coordinate ' + token)
    values = []
    for token in (root.findtext('values') or '').split():
        repeated = re.fullmatch(r'([+-]?\d+|\*)x(\d+)', token)
        values.extend([repeated[1]] * int(repeated[2]) if repeated else [token])
    if len(names) != len(values):
        raise ValueError('complete source coordinate/value cardinality differs')
    assignment, completed = {}, []
    for name, value in zip(names, values):
        if name not in reader.variables:
            if value != '*':
                raise ValueError('nonexistent array coordinate must have wildcard value')
            continue
        if name in assignment:
            raise ValueError('duplicate source witness coordinate')
        if value == '*':
            if not reader.domains[name]:
                raise ValueError('wildcard source coordinate has empty domain')
            value = reader.domains[name][0][0]
            completed.append(name)
        elif not re.fullmatch(r'[+-]?\d+', value):
            raise ValueError('noninteger source witness value')
        assignment[name] = int(value)
    witness = typed(assignment)
    exact_values(witness, reader)
    costs = root.get('cost', '').split()
    if len(costs) != len(directions) or any(not re.fullmatch(r'[+-]?\d+', c) for c in costs):
        raise ValueError('source objective vector missing or wrong cardinality')
    costs = [int(c) for c in costs]
    return dict(status='sat', optimal=status == 'OPTIMUM FOUND', directions=directions,
                witness=witness, original_objective_values=[{'type': 'int', 'value': str(c)} for c in costs],
                signed_objective_values=[{'type': 'int', 'value': str(c if d == 'minimize' else -c)}
                                         for c, d in zip(costs, directions)],
                wildcard_completion_requiring_independent_recheck=completed)


def instantiation(witness, reader, costs):
    values = exact_values(witness, reader)
    root = ET.Element('instantiation')
    if costs:
        if any(row.get('type') != 'int' for row in costs):
            raise ValueError('XCSP objective value must be an exact integer')
        root.set('cost', ' '.join(str(int(row['value'])) for row in costs))
    ET.SubElement(root, 'list').text = ' '.join(reader.variables)
    ET.SubElement(root, 'values').text = ' '.join(str(values[name]) for name in reader.variables)
    return ET.tostring(root, encoding='utf-8')


def check_witness(xml_path, witness, reader, costs, java, jar, output):
    output = Path(output)
    solution = output.with_suffix('.xml')
    solution.write_bytes(instantiation(witness, reader, costs))
    argv = [str(java), '-ea', '-XX:ActiveProcessorCount=1', '-cp', str(jar),
            'org.xcsp.parser.callbacks.SolutionChecker', str(xml_path), str(solution)]
    with output.with_suffix('.stdout').open('wb') as stdout, output.with_suffix('.stderr').open('wb') as stderr:
        result = subprocess.run(argv, stdout=stdout, stderr=stderr)
    text = output.with_suffix('.stdout').read_text()
    errors = output.with_suffix('.stderr').read_text()
    lines = text.splitlines()
    passed = (result.returncode == 0 and sum(bool(re.fullmatch(r'OK(?:\s+-?\d+)?\s*', line)) for line in lines) == 1
              and not any(token in text or token in errors for token in ('INVALID', 'ERROR', 'Exception', 'not implemented')))
    return dict(passed=passed, returncode=result.returncode, argv=argv,
                source_constraints='all original XML constraints and declared domains',
                original_objective_values_checked=costs, witness_coordinates=len(witness))
