"""Closed-input language configurations for natural-language proposals.

These are formal data languages, never Python or shell programs. Their own
frontends remain responsible for supported syntax and semantic elaboration.
"""
import re

from ._nl_model import MAX_TEXT, ModelError

SCHEMA = "somt-nl-formal-v1"
LANGUAGES = ("minizinc", "lp", "xcsp3", "smtlib2")


def formal_schema(language, *, max_program_chars=MAX_TEXT):
    if language not in LANGUAGES:
        raise ModelError("no closed-input NL configuration for " + str(language))
    program_schema = {"type": "string", "minLength": 1}
    if max_program_chars is not None:
        program_schema["maxLength"] = max_program_chars
    return {
        "type": "object",
        "additionalProperties": False,
        "required": [
            "schema",
            "language",
            "program",
            "decision",
            "assumptions",
            "unresolved",
            "links",
        ],
        "properties": {
            "schema": {"const": SCHEMA},
            "language": {"const": language},
            "program": program_schema,
            "decision": {"enum": ["satisfiability", "optimization"]},
            "assumptions": {"type": "array", "items": {"type": "string"}},
            "unresolved": {"type": "array", "items": {"type": "string"}},
            "links": {
                "type": "array",
                "items": {
                    "type": "object",
                    "additionalProperties": False,
                    "required": ["span", "fragment"],
                    "properties": {
                        "span": {
                            "type": "array",
                            "items": {"type": "integer"},
                            "minItems": 2,
                            "maxItems": 2,
                        },
                        "fragment": {
                            "type": "string",
                            "minLength": 1,
                            "description": "An exact substring of program, NOT a quotation or paraphrase of the natural-language source.",
                        },
                    },
                },
            },
        },
    }


def validate_formal(model, source, *, max_program_chars=MAX_TEXT):
    required = {
        "schema",
        "language",
        "program",
        "decision",
        "assumptions",
        "unresolved",
        "links",
        "context",
    }
    if (
        not isinstance(model, dict)
        or set(model) != required
        or model["schema"] != SCHEMA
    ):
        raise ModelError("invalid formal candidate fields")
    language = model["language"]
    formal_schema(language, max_program_chars=max_program_chars)
    if model["decision"] not in ("satisfiability", "optimization"):
        raise ModelError("unsupported decision for this language configuration")
    for key in ("assumptions", "unresolved"):
        if not isinstance(model[key], list) or any(
            not isinstance(x, str) for x in model[key]
        ):
            raise ModelError(key + " must be a list of strings")
    if model["unresolved"]:
        raise ModelError("unresolved: " + "; ".join(model["unresolved"]))
    context = model["context"]
    if not isinstance(context, dict) or any(
        not isinstance(k, str) or not isinstance(v, str) for k, v in context.items()
    ):
        raise ModelError("context must map names to explicit semantic descriptions")
    program = model["program"]
    if (
        not isinstance(program, str)
        or not program.strip()
        or (max_program_chars is not None and len(program) > max_program_chars)
        or "\x00" in program
    ):
        raise ModelError("expected a nonempty bounded formal program")
    # Conservative token denial includes comments/strings deliberately. No
    # generated model may read companion files. Built-in globals need no include
    # in SOMTParser; users of the native MiniZinc oracle add stdlib includes there.
    if language == "minizinc" and re.search(r"\binclude\b", program):
        raise ModelError(
            "inline MiniZinc candidates cannot include files; built-in globals need no include"
        )
    if language == "xcsp3" and re.search(r"<!\s*(DOCTYPE|ENTITY)", program, re.I):
        raise ModelError("XCSP3 candidates cannot declare external entities or DTDs")
    if language == "smtlib2" and re.search(r"\(\s*(include|set-option)\b", program):
        raise ModelError(
            "inline SMT candidates cannot include files or change solver options"
        )
    links = model["links"]
    if not isinstance(links, list) or not links:
        raise ModelError("formal candidate needs source links")
    for link in links:
        if not isinstance(link, dict) or set(link) != {"span", "fragment"}:
            raise ModelError("invalid source link")
        span = link["span"]
        if (
            not isinstance(span, list)
            or len(span) != 2
            or any(type(x) is not int for x in span)
            or not 0 <= span[0] < span[1] <= len(source)
        ):
            raise ModelError("invalid source code-point span")
        if (
            not isinstance(link["fragment"], str)
            or not link["fragment"]
            or link["fragment"] not in program
        ):
            raise ModelError("source link must identify an actual formal fragment")
    return program, language
