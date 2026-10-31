"""Located validation feedback; never repair or reinterpret a candidate here."""
import re


def _tokens(path):
    if path == 'model':
        return []
    if path.startswith('model.'):
        path = path[len('model.'):]
    identifier = r'[A-Za-z_][A-Za-z_0-9]*'
    if not re.fullmatch(identifier + r'(?:\.' + identifier + r'|\[(?:0|[1-9][0-9]*)\])*', path):
        return None
    return [name if name else int(index) for name, index in
            re.findall(r'(' + identifier + r')|\[([0-9]+)\]', path)]


def _located(source, model, path, message, diagnostic_index, kind):
    tokens = _tokens(path) if path is not None else None
    detail = dict(kind=kind, diagnostic_index=diagnostic_index, message=message,
                  path=path if tokens is not None else None, json_pointer=None,
                  value_present=False, source_span=None)
    if tokens is None:
        return detail
    detail['json_pointer'] = ''.join('/' + str(item).replace('~', '~0').replace('/', '~1')
                                     for item in tokens)
    current = model
    ancestors = [current]
    present = True
    for token in tokens:
        if isinstance(token, str) and isinstance(current, dict) and token in current:
            current = current[token]
        elif type(token) is int and isinstance(current, list) and token < len(current):
            current = current[token]
        else:
            present = False
            break
        ancestors.append(current)
    detail['value_present'] = present
    if present:
        detail['value_type'] = {type(None): 'null', bool: 'boolean', int: 'integer',
                                float: 'number', str: 'string', list: 'array',
                                dict: 'object'}.get(type(current), 'unknown')
        # The complete immutable candidate is already sent once in repair.
        # Avoid duplicating arbitrarily large expressions or root models.
        if current is None or type(current) in (bool, int, float):
            detail['value'] = current
        elif isinstance(current, str):
            if len(current) <= 512:
                detail['value'] = current
            else:
                detail['value_excerpt'] = current[:512]
                detail['value_excerpt_truncated'] = True
    # Explain this common constructor mismatch without executing a repair.
    # The nested object remains invalid; its type and lexical scope still need
    # the ordinary validator after the provider chooses a revised expression.
    if (present and kind == 'construction' and tokens and tokens[-1] == 'literal'
            and isinstance(current, dict) and len(ancestors) >= 2
            and isinstance(ancestors[-2], dict)
            and set(ancestors[-2]) == {'literal', 'sort'}
            and current.keys() & {'literal', 'var', 'cp', 'op', 'op_indexed', 'at', 'data', 'apply',
                                  'fold', 'quantifier', 'const_array', 'tuple',
                                  'tuple_unit', 'dt_constructor', 'dt_selector',
                                  'dt_tester', 'rm'}):
        detail['construction_hint'] = {
            'code': 'expression-in-literal',
            'message': ('A literal encodes a constant value, not an expression object. '
                        'Place the nested literal, variable reference, or computed expression at the '
                        'enclosing expression position. Preserve its expected sort and lexical '
                        'binders; do not infer new declarations or quantifiers.'),
            'expression_json_pointer': detail['json_pointer'].removesuffix('/literal'),
            'automatic_repair': False,
        }
    # These are encoding hints for a diagnosed Real constant, never coercions.
    # In particular, replacing an identifier-looking coefficient with a variable
    # could turn c*x into x*x; its intended role must be checked against source.
    if (present and kind == 'construction' and tokens and tokens[-1] == 'literal'
            and message == 'real literals must be exact decimal/rational strings'
            and len(ancestors) >= 2 and isinstance(ancestors[-2], dict)
            and set(ancestors[-2]) == {'literal', 'sort'}
            and ancestors[-2]['sort'] == 'Real'):
        hint = None
        if type(current) is int:
            hint = dict(
                code='real-integer-encoding',
                message=('Real constants use exact decimal/rational strings, including whole numbers. '
                         'If this integer is the intended source coefficient, encode the same integer '
                         'as a string; retain Real sort. Do not convert through floating point or '
                         'change the declaration domain.'),
            )
            # Keep feedback bounded, as for the located scalar excerpt above.
            if current.bit_length() <= 1024:
                hint['same_value_literal'] = dict(literal=str(current), sort='Real')
        elif isinstance(current, str) and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', current):
            hint = dict(
                code='identifier-in-real-literal',
                message=('This identifier is not an exact Real constant. Check the entire enclosing '
                         'expression against the source: a variable uses {"var": "name"}, whereas '
                         'a coefficient uses an exact numeric string. A lone quantity needs no '
                         'multiplication; an explicit unit coefficient is "1". Replacing a malformed '
                         'coefficient with a variable can introduce an unintended product or square. '
                         'Do not guess a coefficient, create a declaration, or change a bound.'),
            )
        if hint is not None:
            hint['expression_json_pointer'] = detail['json_pointer'].removesuffix('/literal')
            hint['automatic_repair'] = False
            detail['construction_hint'] = hint
    for parent in reversed(ancestors):
        span = parent.get('span') if isinstance(parent, dict) else None
        if (isinstance(span, list) and len(span) == 2
                and all(type(part) is int for part in span)
                and 0 <= span[0] < span[1] <= len(source)):
            detail['source_span'] = list(span)
            excerpt = source[span[0]:span[1]]
            detail['source_excerpt'] = excerpt[:512]
            detail['source_excerpt_truncated'] = len(excerpt) > 512
            detail['source_span_origin'] = 'candidate-annotation'
            break
    return detail


def validation_feedback(source, model, diagnostics):
    """Return fresh, non-executable details for the existing validator messages.

    Recognize only the validator's restricted dotted/indexed path syntax.
    Unknown or native-only locations remain unlocated; never infer a path from
    words inside an error. Ordinary diagnostics remain authoritative and intact.
    Unresolved alternatives are indexed individually, without deciding whether
    any is a genuine ambiguity or changing compilation's refusal.
    """
    unresolved = model.get('unresolved') if isinstance(model, dict) else None
    refusal_messages = set()
    if isinstance(unresolved, list) and unresolved and all(isinstance(item, str) for item in unresolved):
        joined = '; '.join(unresolved)
        refusal_messages = {'model: unresolved interpretation: ' + joined,
                            'unresolved: unresolved interpretations: ' + joined,
                            'model: unresolved: ' + joined}
    output = []
    for index, diagnostic in enumerate(diagnostics):
        if diagnostic in refusal_messages:
            output.extend(_located(source, model, f'unresolved[{position}]', item, index,
                                   'unresolved_interpretation')
                          for position, item in enumerate(unresolved))
            continue
        path, separator, message = diagnostic.partition(': ')
        recognized = bool(separator) and _tokens(path) is not None
        output.append(_located(source, model, path if recognized else None,
                               message if recognized else diagnostic, index,
                               'construction' if recognized else 'validation'))
    return output
