"""Lexical observation maps never consult coefficient or solver evidence."""
import copy
import json
from pathlib import Path

from tools.semantic_checks.nl4opt_lexical_alignment import align


def declarations(*names):
    return [dict(name=name, sort="Real", lower="0") for name in names]


SOURCE = "Make containers of Oil Max and Oil Max Pro."
ALIASES = {"Oil Max": 0, "Oil Max Pro": 1}
NAMES = declarations("oil_max_containers", "oil_max_pro_containers")


def test_official_oil_max_complete_source_names():
    fixture = Path(__file__).parents[1] / "fixtures/nl4opt_oil_max_source_names.json"
    record = json.loads(fixture.read_text())
    result = align(record["source"], record["declarations"], record["aliases"])
    assert result["status"] == "lexically-aligned"
    assert result["variable_map"] == {"0": "oil_max_containers", "1": "oil_max_pro_containers"}
    assert result["edges"]["oil_max_pro_containers"] == [{
        "coordinate": 1, "alias": "Oil Max Pro",
        "rule": "source-phrase-with-quantity-suffix",
        "matched_phrase": ["oil", "max", "pro"],
        "quantity_suffix": ["container"],
        "source_token_positions": result["edges"]["oil_max_pro_containers"][0]["source_token_positions"],
    }]
    assert result["edges"]["oil_max_pro_containers"][0]["source_token_positions"]


def test_longest_complete_name_retains_quantity_like_entity_word():
    result = align("Sell Apple and Apple Box.",
                   declarations("apple_units", "apple_box_units"),
                   {"Apple": 0, "Apple Box": 1})
    assert result["variable_map"] == {"0": "apple_units", "1": "apple_box_units"}


def test_exact_full_name_precedes_suffix_stripping():
    result = align("Choose oil and oil units.", declarations("oil", "oil_units"),
                   {"oil": 0, "oil units": 1})
    assert result["variable_map"] == {"0": "oil", "1": "oil_units"}
    assert result["edges"]["oil_units"][0]["rule"] == "exact-normalized"


def test_near_names_with_unrecognized_tail_remain_ambiguous():
    result = align(SOURCE, declarations("oil_max_containers", "oil_max_pro_flavor"), ALIASES)
    assert result["reason"] == "ambiguous-lexical-match"
    assert result["variable_map"] == {}


def test_scattered_source_tokens_do_not_prove_complete_name():
    result = align("Oil Max is oil. Max is advertised as pro.", NAMES, ALIASES)
    assert result["reason"] == "ambiguous-lexical-match"
    assert result["variable_map"] == {}


def test_phrase_order_is_preserved():
    result = align("Oil Max and Max Pro Oil come in containers.", NAMES, ALIASES)
    assert result["reason"] == "ambiguous-lexical-match"
    assert result["variable_map"] == {}


def test_equal_specificity_different_coordinates_is_refused():
    aliases = {"Oil Max": 0, "Oil Max Pro": 1, "oil max pro": 0}
    result = align(SOURCE, NAMES, aliases)
    assert result["reason"] == "ambiguous-lexical-match"
    assert result["variable_map"] == {}


def test_duplicate_aliases_for_one_coordinate_are_harmless():
    result = align(SOURCE, NAMES, dict(ALIASES, **{"oil max pro": 1}))
    assert result["variable_map"] == {"0": "oil_max_containers", "1": "oil_max_pro_containers"}


def test_different_names_cannot_collapse_to_one_coordinate():
    result = align(SOURCE, declarations("oil_max_containers", "oil_max_units"), ALIASES)
    assert result["reason"] == "nonbijective-lexical-match"
    assert result["variable_map"] == {}


def test_duplicate_candidate_names_are_refused():
    result = align(SOURCE, declarations("oil_max_containers", "oil_max_containers"), ALIASES)
    assert result["reason"] == "duplicate-candidate-name"


def test_missing_entity_cannot_be_inferred_from_bijection():
    result = align(SOURCE, declarations("oil_max_containers", "unknown_containers"), ALIASES)
    assert result["reason"] == "missing-lexical-match"
    assert result["variable_map"] == {}


def test_more_than_one_quantity_suffix_is_supported():
    result = align(SOURCE, declarations("oil_max_container_count", "oil_max_pro_container_count"), ALIASES)
    assert result["variable_map"] == {"0": "oil_max_container_count", "1": "oil_max_pro_container_count"}


def test_declaration_and_alias_order_do_not_fit_a_permutation():
    forward = align(SOURCE, NAMES, ALIASES)
    reverse = align(SOURCE, list(reversed(NAMES)), dict(reversed(list(ALIASES.items()))))
    assert forward["variable_map"] == reverse["variable_map"]
    assert forward["permutation_search"] is reverse["permutation_search"] is False


def test_numeric_text_and_annotations_do_not_choose_mapping_or_mutate_inputs():
    names = copy.deepcopy(NAMES)
    names[0]["coefficient"] = {"unreadable_to_float": object()}
    before = [(row["name"], row["sort"], row["lower"]) for row in names]
    a = align(SOURCE + " The profits are 10 and 15.", names, ALIASES)
    b = align(SOURCE + " The profits are 1500 and -2.", names, ALIASES)
    assert a["variable_map"] == b["variable_map"]
    assert a["formula_or_outcome_access"] is b["formula_or_outcome_access"] is False
    assert before == [(row["name"], row["sort"], row["lower"]) for row in names]
