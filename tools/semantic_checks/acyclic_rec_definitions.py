"""Normalize acyclic ``define-fun-rec`` commands before projection.

SOMTParser may retain a large, acyclic helper using ``define-fun-rec`` to avoid
macro expansion in emitted SMT-LIB. Z3 then exposes an uninterpreted recursive
declaration to AST-only consumers, even though its semantics are just the
unique nonrecursive definition. This source-level pass changes only singleton
recursive definitions proven not to lie on a cycle in the complete function
definition dependency graph. Recursive definitions and groups stay byte-for-
byte unchanged.

The pass is deliberately syntactic and conservative: malformed scripts or
unsupported command shapes are returned unchanged. Only the command keyword
of a proven acyclic singleton definition is replaced; all bodies and assertions
remain byte-identical.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class _Atom:
    text: str
    start: int
    end: int


class _List(list):
    def __init__(self, values, start, end):
        super().__init__(values)
        self.start = start
        self.end = end


def _tokens(script):
    """Yield ``(kind, text, start, end)`` with SMT-LIB comments/quotes handled."""
    i, n = 0, len(script)
    while i < n:
        ch = script[i]
        if ch.isspace():
            i += 1
            continue
        if ch == ';':
            newline = script.find('\n', i)
            i = n if newline < 0 else newline + 1
            continue
        if script.startswith('#|', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if script.startswith('#|', i):
                    depth += 1
                    i += 2
                elif script.startswith('|#', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated SMT-LIB block comment')
            continue
        start = i
        if ch in '()':
            i += 1
            yield ch, ch, start, i
            continue
        if ch == '"':
            i += 1
            while i < n:
                if script[i] == '"':
                    i += 1
                    if i < n and script[i] == '"':
                        i += 1
                        continue
                    break
                i += 1
            else:
                raise ValueError('unterminated SMT-LIB string')
            yield 'atom', script[start:i], start, i
            continue
        if ch == '|':
            i += 1
            while i < n:
                if script[i] == '\\' and i + 1 < n:
                    i += 2
                elif script[i] == '|':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('unterminated quoted SMT-LIB symbol')
            yield 'atom', script[start:i], start, i
            continue
        while i < n and not script[i].isspace() and script[i] not in '();':
            i += 1
        if i == start:
            raise ValueError('invalid SMT-LIB token')
        yield 'atom', script[start:i], start, i


def _parse(script):
    """Parse balanced SMT-LIB lists iteratively, retaining source offsets."""
    root, stack = [], []
    for kind, text, start, end in _tokens(script):
        if kind == '(':
            stack.append((start, []))
        elif kind == ')':
            if not stack:
                raise ValueError('unmatched closing parenthesis')
            list_start, values = stack.pop()
            node = _List(values, list_start, end)
            (stack[-1][1] if stack else root).append(node)
        else:
            atom = _Atom(text, start, end)
            (stack[-1][1] if stack else root).append(atom)
    if stack:
        raise ValueError('unclosed SMT-LIB list')
    return root


def _atom(node):
    return node.text if isinstance(node, _Atom) else None


def _applications(node, names):
    """Collect calls to known function definitions, iteratively."""
    found, pending = set(), [node]
    while pending:
        current = pending.pop()
        if isinstance(current, _List):
            if current and _atom(current[0]) in names:
                found.add(_atom(current[0]))
            pending.extend(current)
    return found


def normalize_acyclic_recursive_definitions(script):
    """Rewrite only singleton recursive definitions with no dependency cycle.

    ``define-funs-rec`` groups are never rewritten. For a singleton function,
    acyclicity is checked over calls to every top-level ordinary or recursive
    definition, including indirect paths through ordinary helpers.
    """
    if not isinstance(script, str):
        raise TypeError('SMT-LIB input must be text')
    try:
        forms = _parse(script)
    except ValueError:
        return script

    definitions = {}
    ambiguous_names = set()

    def register(name, body):
        if name in definitions:
            ambiguous_names.add(name)
        else:
            definitions[name] = body

    recursive_singletons = {}
    for form in forms:
        if not isinstance(form, _List) or not form:
            continue
        command = _atom(form[0])
        if command in ('define-fun', 'define-fun-rec') and len(form) == 5:
            name = _atom(form[1])
            if name is None:
                continue
            register(name, form[4])
            if command == 'define-fun-rec':
                recursive_singletons[name] = (form, form[0])
        elif command == 'define-funs-rec' and len(form) == 3 and isinstance(form[1], _List) and isinstance(form[2], _List):
            declarations, bodies = form[1], form[2]
            if len(declarations) != len(bodies):
                continue
            for declaration, body in zip(declarations, bodies):
                name = _atom(declaration[0]) if isinstance(declaration, _List) and declaration else None
                if name is not None:
                    register(name, body)

    # Duplicate declarations make the dependency graph ambiguous. Keep the
    # original script intact rather than guessing which body a call denotes.
    if ambiguous_names:
        return script

    if not recursive_singletons:
        return script

    names = set(definitions)
    edges = {name: _applications(body, names)
             for name, body in definitions.items()}

    def is_acyclic_from(start):
        pending = list(edges.get(start, ()))
        visited = set()
        while pending:
            current = pending.pop()
            if current == start:
                return False
            if current not in visited:
                visited.add(current)
                pending.extend(edges.get(current, ()))
        return True

    replacements = []
    for name, (form, command_atom) in recursive_singletons.items():
        if is_acyclic_from(name):
            replacements.append((command_atom.start, command_atom.end, 'define-fun'))
    if not replacements:
        return script
    for start, end, replacement in sorted(replacements, reverse=True):
        script = script[:start] + replacement + script[end:]
    return script
