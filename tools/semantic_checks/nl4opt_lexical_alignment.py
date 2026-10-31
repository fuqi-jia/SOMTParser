"""Source/identifier-only alignment; no formulas, coefficients, or solver access."""
import re
import unicodedata

VERSION = 'source-lexical-bijection-v2'
# These quantity suffixes do not identify an entity by themselves. They are
# removed only from candidate names during the weaker, source-grounded rule.
QUANTITY_WORDS = frozenset({'amount', 'number', 'num', 'count', 'quantity', 'qty',
    'unit', 'hour', 'minute', 'investment', 'dollar', 'spent', 'produced', 'made',
    'purchased', 'bought', 'sold', 'used'})


def tokens(text):
    text = re.sub(r'([a-z])([A-Z])', r'\1 \2', unicodedata.normalize('NFKC', text))
    raw = re.findall(r'[a-z]+|[0-9]+', text.casefold())
    result = []
    for word in raw:
        if len(word) > 4 and word.endswith('ies'):
            word = word[:-3] + 'y'
        elif word.endswith(('ches', 'shes', 'xes', 'zes', 'sses')):
            word = word[:-2]
        elif word == 'buses':
            word = 'bus'
        elif len(word) > 3 and word.endswith('s') and not word.endswith(('ss', 'us', 'is')):
            word = word[:-1]
        result.append(word)
    return tuple(result)


# These suffixes describe an amount of an already named entity. They are used
# only after exact-name matching and only when the remaining complete alias is
# an ordered phrase in the source. The weaker token-subset rule is unchanged.
QUANTITY_SUFFIX_WORDS = QUANTITY_WORDS | frozenset({
    'bag', 'bottle', 'box', 'container', 'package', 'pack', 'batch', 'trip',
    'gram', 'kilogram', 'liter', 'litre', 'gallon', 'pound', 'kg', 'lb',
})


def _quantity_suffix_matches(words, source_words, normalized_aliases):
    """Match the longest complete source phrase before quantity suffixes.

    This is a lexical priority rule, not a permutation or formula search. Try
    the longest prefix first: ``apple_box_units`` must prefer an explicit
    ``Apple Box`` alias over ``Apple`` even though both trailing words could
    describe quantities. Ties between coordinates remain ambiguous.
    """
    for end in range(len(words) - 1, 0, -1):
        if words[end] not in QUANTITY_SUFFIX_WORDS:
            break
        core = words[:end]
        matches = []
        for alias, index, alias_words in normalized_aliases:
            if core != alias_words:
                continue
            occurrences = [position for position in range(len(source_words)-len(core)+1)
                           if source_words[position:position+len(core)] == core]
            if occurrences:
                matches.append({'coordinate': index, 'alias': alias,
                    'rule': 'source-phrase-with-quantity-suffix',
                    'matched_phrase': list(core),
                    'quantity_suffix': list(words[end:]),
                    'source_token_positions': occurrences})
        if matches:
            return matches
    return []


def align(source, declarations, aliases):
    """Accept only a complete bijection with one lexical choice per declaration.

    No permutation search or semantic score is used. A source-only preview may
    call this function, but the evaluator must call it again after compilation.
    """
    report = {'method': VERSION, 'status': 'observation-alignment-required',
              'variable_map': {}, 'edges': {}, 'source_only': True,
              'formula_or_outcome_access': False, 'permutation_search': False}
    if not isinstance(aliases, dict) or not aliases:
        return dict(report, reason='missing-reference-aliases')
    if any(not isinstance(name, str) or type(index) is not int or index < 0
           for name, index in aliases.items()):
        return dict(report, reason='malformed-reference-aliases')
    coordinates = set(aliases.values())
    if coordinates != set(range(len(coordinates))):
        return dict(report, reason='noncontiguous-reference-coordinates')
    if (not isinstance(declarations, list) or
            any(not isinstance(row, dict) or not isinstance(row.get('name'), str)
                or row.get('sort') != 'Real' or row.get('shape', []) != [] for row in declarations)):
        return dict(report, reason='scalar-real-declarations-required')
    names = [row['name'] for row in declarations]
    report.update(candidate_names=names, reference_coordinate_count=len(coordinates))
    if len(set(names)) != len(names):
        return dict(report, reason='duplicate-candidate-name')
    if len(names) != len(coordinates):
        return dict(report, reason='coordinate-count-mismatch')
    source_tokens = tokens(source)
    source_words = set(source_tokens)
    normalized_aliases = [(name, index, tokens(name)) for name, index in aliases.items()]
    for name in names:
        words = tokens(name)
        exact = []
        for alias, index, alias_words in normalized_aliases:
            if words and alias_words and (words == alias_words or ''.join(words) == ''.join(alias_words)):
                exact.append({'coordinate': index, 'alias': alias, 'rule': 'exact-normalized'})
        edges = exact
        if not edges:
            edges = _quantity_suffix_matches(words, source_tokens, normalized_aliases)
        if not edges:
            content = set(words) - QUANTITY_WORDS
            edges = []
            for alias, index, alias_words in normalized_aliases:
                entity = set(alias_words)
                shared = content & entity
                if (content and entity and shared and shared.issubset(source_words)
                        and (content.issubset(entity) or entity.issubset(content))):
                    edges.append({'coordinate': index, 'alias': alias,
                                  'rule': 'source-grounded-token-subset', 'shared_tokens': sorted(shared)})
        report['edges'][name] = edges
    choices = {name: sorted({edge['coordinate'] for edge in edges})
               for name, edges in report['edges'].items()}
    report['choices'] = choices
    if any(not values for values in choices.values()):
        return dict(report, reason='missing-lexical-match')
    if any(len(values) != 1 for values in choices.values()):
        return dict(report, reason='ambiguous-lexical-match')
    mapping = {str(values[0]): name for name, values in choices.items()}
    if len(mapping) != len(names) or {int(key) for key in mapping} != coordinates:
        return dict(report, reason='nonbijective-lexical-match')
    return dict(report, status='lexically-aligned', reason='unique-complete-bijection', variable_map=mapping)
