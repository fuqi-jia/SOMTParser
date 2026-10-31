"""Natural language -> reviewed typed candidate -> existing semantic pipeline.

The built-in provider implements a documented controlled grammar. External
providers return a typed JSON model or a closed-input formal-language model. Their
candidate digest must be explicitly selected before compilation.
"""
import argparse
import copy
from dataclasses import dataclass
from fractions import Fraction
import hashlib
from importlib import resources
import json
from pathlib import Path
import sys
from typing import Any, Callable, Dict, Mapping, Optional, Tuple

from ._nl_controlled import propose_controlled
from ._nl_model import (MAX_TEXT, ModelError, compile_model,
                        IDENTIFIER_RULES, TERM_NAMESPACE_RULES)
from ._hir_modeling import MODELING_GUIDANCE
from ._nl_formal import SCHEMA as FORMAL_SCHEMA, formal_schema, validate_formal
from .hir import SCHEMA as HIR_SCHEMA, hir_schema, build_hir
from .hir_canonical import canonicalize_hir
from ._nl_feedback import validation_feedback

Provider = Callable[[Mapping[str, Any]], Mapping[str, Any]]
_CHOICE_AND_OBJECTIVE_GUIDANCE = (
    " If a solution may use any one admissible choice or operation order, encode the alternatives with OR "
    "or an existentially selected branch. Do not require every alternative simultaneously with AND. "
    "Keep requirements that apply to all choices outside that disjunction; use AND for simultaneous requirements. "
    "A stated known optimum or target bound is a hard constraint when the task asks for an arrangement satisfying "
    "that bound; it is not permission to replace the bound with an optimization objective. Add an objective only "
    "when the source or context requests optimization, and keep every explicitly required bound hard. "
    "Distinguish maximal (no allowed extension) from maximum (largest objective value); do not add maximum "
    "optimization merely because the source requests a maximal solution."
)
_SOURCE_RELATION_GUIDANCE = (
    " Preserve the full feasible relation over source-visible assignments and their objective values. "
    "When a numerical quantity should be closest to a target, minimize its absolute deviation unless the source "
    "specifies another distance or a one-sided requirement. Do not silently impose quantity <= target or "
    "quantity >= target. Keep the requested cost on every feasible assignment, including non-optimal ones: "
    "do not substitute an offset, rescaled, or order-equivalent proxy merely because it selects the same optimum. "
    "A requested number of distinct values is a distinct count, not the largest value or label unless the source "
    "entails that equality. "
    "For association arrays, identify each axis's entities, the meaning of each stored value, and the direction "
    "of the mapping. Preserve the source/context's requested output representation. An entity-to-identifier "
    "array and its inverse row-to-category table are different outputs even if they describe the same associations. "
    "If an internal representation is inverted, channel it to the required outputs explicitly; retaining the "
    "same names and shapes does not make the coordinate map an identity. Record genuinely unspecified mapping "
    "conventions in unresolved rather than silently choosing one. "
    "Do not add symmetry-breaking or canonical-label constraints, or tighten source-visible domains, "
    "solely because they preserve an optimum or simplify solving. Add such restrictions only when "
    "the source or context explicitly requests canonical solutions or logically entails the domain bound. "
    "For grid models, keep supplied observations or clues distinct from unknown decision cells. When source "
    "semantics say an opened or numbered cell is safe, explicitly constrain its mine indicator to false; "
    "do not infer safety for other cells. For an adjacency count, enumerate each in-bounds neighbor once, "
    "exclude the center when adjacency excludes it, and do not wrap at grid edges unless the source says so. "
    "In HIR, use Bool-valued expressions directly as conditions or combine them with Boolean operators. "
    "Use eq/ne when Bool equality is required; lt/le/gt/ge require numeric operands and must never compare "
    "a Bool term with true or false. "
    "Match JSON literal values to their declared HIR sort: an Int literal must be a JSON integer, not a "
    "Boolean or floating-point number. Do not round, truncate, or silently cast a value between sorts. "
    'A declared variable is referenced with {"var":"name"}, including Real variables; never put its name in literal. '
    "Place a nested literal node or a computed expression directly at its operand position, not inside another literal node. "
    'A Real literal is an exact numeric string such as {"literal":"3/2","sort":"Real"}; '
    'encode arithmetic with op/args rather than embedding an expression or units in that numeric string. '
    "An ite condition must have Bool sort; do not use an Int indicator directly as a condition. Use a Bool "
    "expression, or compare an Int indicator with a value only when that relationship is supported by the source. "
    "An HIR Int quantifier ranges over all mathematical integers. For a source statement over a finite range, "
    "encode forall i: in_range(i) implies property(i), whereas an existential witness uses exists i: "
    "in_range(i) and property(i). Put every range and its body inside the same binder scope. Array shape "
    "does not restrict a bound Int variable. Use the source's exact endpoints, or a documented finite fold "
    "when appropriate; never conjoin a finite range with the body of an unrestricted universal quantifier. "
    "Interpret stated capacity as an upper bound (<=) unless the source explicitly requires filling it exactly. "
    "For percentages and ratios, identify the compared quantities, denominator, and units before writing coefficients. "
    "If X is at least a fraction p of total X+Y, encode X >= p*(X+Y); for 0<p<1 the equivalent form is X >= p/(1-p)*Y, "
    "not X >= p/(1-p)*(X+Y). The same denominator rule applies to upper bounds. A count ratio X >= k*Y uses counts alone; "
    "do not import unrelated cost, space, weight, or capacity coefficients into it. Preserve exact rational p. "
    "Phrases such as can hold, can fit, or can be printed describe capacity, not a requirement to use every slot. "
    "Treat counts or lengths that define an array's index set (such as the number of categories) as shape metadata, "
    "not as per-cell value bounds. Add a per-cell maximum only when the source or context states it or logically entails it. "
    "When the source explicitly says an omitted value, label, or operator is unknown to be determined and gives a finite "
    "set of choices, model the choice as a decision (for example, a finite-domain variable or a disjunction) and constrain "
    "each branch. Do not put that explicit choice in unresolved. Keep unresolved for genuinely unspecified semantics of how "
    "a chosen operation applies, such as an operand order the source never defines."
    + _CHOICE_AND_OBJECTIVE_GUIDANCE
)

_HIR_COVERAGE_GUIDANCE = (
    "Before returning the model, make a private coverage inventory from the source: every decision and output name/shape, "
    "domain, instance-data row, independent constraint (including each row, column, diagonal, window, tuple, and boundary case), "
    "objective sense and exact objective definition, and requested observable. Map every item to a declaration, constraint, "
    "objective, or output shape with a source span. Check that no item was only described in assumptions or interpretation_notes, or left out because "
    "its encoding is lengthy. Prefer exact finite folds and the documented compact globals for repeated patterns. Do not add "
    "symmetry breaking or narrow domains to make the model easier. Keep genuinely conflicting source readings in unresolved; "
    "complexity, an omitted table, or an unfinished encoding is not a source ambiguity. If an actual API limitation prevents "
    "an exact encoding, identify that limitation explicitly rather than returning a partial model as complete."
)

_HIR_CONSTRUCTOR_GUIDANCE = (
    " " + IDENTIFIER_RULES + " " + TERM_NAMESPACE_RULES + " " +
    "For all-different over every cell of a declared shaped Int array, use native HIR "
    '{"op":"all_different","args":[{"var":"array_name"}]} or list every scalar cell explicitly. A CP vector descriptor '
    '{"array":"name","length":n,"prefix":[...]} indexes only the final axis after its fixed prefix; length must not exceed '
    "that final-axis size. Never use total cell count as length for a multidimensional array. For CP table, provide the required "
    'Boolean field positive: true means tuples are allowed, false means listed tuples are forbidden; choose polarity from the source. '
    "Do not infer or omit table polarity."
    " Use cp circuit only for a tour visiting every vertex. cp subcircuit permits inactive self-successors and requires "
    "all other vertices to form one cycle; supply its required allow_empty Boolean from the source. A union of multiple "
    "nontrivial cycles is a different relation. Do not silently replace any of these relations with another."
)

# Model payloads and serialized envelopes have different sizes: the envelope
# also carries source text and normalization history. In particular, legacy
# pretty printing must not make a candidate impossible to load back.
MAX_MODEL_JSON = 16 * 1024 * 1024
MAX_ENVELOPE_JSON = 3 * MAX_MODEL_JSON


@dataclass(frozen=True)
class CandidateSizeLimits:
    """Explicit character budgets for candidate input and serialization.

    Defaults preserve the public API's existing safeguards. Set either field
    to ``None`` only when a caller deliberately accepts an unbounded input.
    The envelope limit defaults to the historical cap unless larger source or
    model limits require a correspondingly larger envelope.
    """

    max_source_chars: Optional[int] = MAX_TEXT
    max_model_json_chars: Optional[int] = MAX_MODEL_JSON
    max_envelope_json_chars: Optional[int] = None

    def __post_init__(self):
        for name in ("max_source_chars", "max_model_json_chars", "max_envelope_json_chars"):
            value = getattr(self, name)
            if value is not None and (type(value) is not int or value < 1):
                raise ModelError(f"{name} must be a positive integer or None")

    @property
    def envelope_limit(self):
        if self.max_envelope_json_chars is not None:
            return self.max_envelope_json_chars
        if self.max_source_chars is None or self.max_model_json_chars is None:
            return None
        derived = self.max_model_json_chars + 6 * self.max_source_chars + 4096
        return max(MAX_ENVELOPE_JSON, derived)


DEFAULT_CANDIDATE_SIZE_LIMITS = CandidateSizeLimits()


@dataclass(frozen=True)
class _ResolvedSizeLimits:
    max_source_chars: Optional[int]
    max_model_json_chars: Optional[int]
    envelope_limit: Optional[int]
    formal_limit: Optional[int]


def _size_limits(value):
    # An explicit candidate policy wins. Otherwise each public operation uses
    # its caller's thread/task context; provider metadata cannot raise it.
    if value is None:
        from .construction_limits import current_construction_limits
        limits = current_construction_limits()
        return _ResolvedSizeLimits(
            limits.max_source_chars, limits.max_model_json_chars,
            limits.max_envelope_json_chars, limits.max_formal_program_chars,
        )
    if not isinstance(value, CandidateSizeLimits):
        raise ModelError("size_limits must be a CandidateSizeLimits value")
    return _ResolvedSizeLimits(
        value.max_source_chars, value.max_model_json_chars,
        value.envelope_limit, value.max_model_json_chars,
    )


def _validate_source_size(source, limit):
    if (not isinstance(source, str) or not source.strip()
            or (limit is not None and len(source) > limit)):
        policy = ("128 Ki-character limit" if limit == MAX_TEXT
                  else "caller's source-character budget")
        raise ModelError(
            "expected nonempty source within the configured character limit (" + policy + ")"
        )


def _size_limits_json(value):
    return {
        "max_source_chars": value.max_source_chars,
        "max_model_json_chars": value.max_model_json_chars,
        "max_envelope_json_chars": value.max_envelope_json_chars,
    }


def _size_limits_from_json(value):
    if not isinstance(value, dict) or set(value) != {
        "max_source_chars", "max_model_json_chars", "max_envelope_json_chars"
    }:
        raise ModelError("invalid candidate size_limits metadata")
    return CandidateSizeLimits(**value)


def _canonical(value):
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )


def _hash(value):
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _is_hir_sort(value):
    if value in ("Bool", "Int", "Real", "String", "RegLan"):
        return True
    if not isinstance(value, dict) or len(value) != 1:
        return False
    key, payload = next(iter(value.items()))
    if key == "Set":
        return _is_hir_sort(payload)
    if key == "BitVec":
        return type(payload) is int and payload > 0
    if key == "FloatingPoint":
        return (isinstance(payload, list) and len(payload) == 2
                and all(type(part) is int and part > 0 for part in payload))
    if key == "Array":
        return (isinstance(payload, list) and len(payload) == 2
                and all(_is_hir_sort(part) for part in payload))
    if key == "Tuple":
        return isinstance(payload, list) and all(_is_hir_sort(part) for part in payload)
    if key in ("Parameter", "Uninterpreted"):
        return isinstance(payload, str) and bool(payload)
    if key == "Datatype":
        return (isinstance(payload, str) and bool(payload)) or (
            isinstance(payload, dict) and set(payload) == {"name", "args"}
            and isinstance(payload["name"], str) and bool(payload["name"])
            and isinstance(payload["args"], list)
            and all(_is_hir_sort(part) for part in payload["args"])
        )
    return False


def _normalize_required_outputs(required_outputs):
    """Validate a caller-supplied, source-derived HIR output contract."""
    if required_outputs is None:
        return []
    if not isinstance(required_outputs, list):
        raise ModelError("required_outputs must be a list of {name, sort, shape} objects")
    normalized = []
    names = set()
    for index, item in enumerate(required_outputs):
        path = f"required_outputs[{index}]"
        if not isinstance(item, dict) or set(item) != {"name", "sort", "shape"}:
            raise ModelError(f"{path} must contain exactly name, sort, and shape")
        name = item["name"]
        sort = item["sort"]
        shape = item["shape"]
        if (not isinstance(name, str) or not name.isidentifier() or len(name) > 128):
            raise ModelError(f"{path}.name must be a HIR identifier")
        if name in names:
            raise ModelError(f"duplicate required output name {name!r}")
        names.add(name)
        if not _is_hir_sort(sort):
            raise ModelError(f"{path}.sort must be a HIR sort")
        if (not isinstance(shape, list) or len(shape) > 8
                or any(type(axis) is not int or axis < 0 for axis in shape)):
            raise ModelError(f"{path}.shape must be a list of at most 8 nonnegative integer extents")
        cells = 1
        for axis in shape:
            cells *= axis
        if cells > 10000:
            raise ModelError(f"{path}.shape exceeds the HIR finite declaration size limit")
        normalized.append({"name": name, "sort": copy.deepcopy(sort), "shape": list(shape)})
    return normalized


def _required_output_diagnostics(model, required_outputs):
    """Compare exact output signatures without repairing or mutating a model."""
    if not required_outputs:
        return ()
    if not isinstance(model, dict) or model.get("schema") != HIR_SCHEMA:
        return ("required_outputs contract applies only to HIR candidates",)
    declarations = model.get("declarations")
    by_name = {}
    if isinstance(declarations, list):
        for declaration in declarations:
            if isinstance(declaration, dict) and isinstance(declaration.get("name"), str):
                by_name.setdefault(declaration["name"], []).append(declaration)
    diagnostics = []
    for output in required_outputs:
        name = output["name"]
        matches = by_name.get(name, [])
        if not matches:
            diagnostics.append(f"required output {name!r} is not declared")
            continue
        if len(matches) != 1:
            diagnostics.append(f"required output {name!r} has {len(matches)} declarations; expected exactly one")
            continue
        declaration = matches[0]
        actual_sort = declaration.get("sort")
        if _canonical(actual_sort) != _canonical(output["sort"]):
            diagnostics.append(
                f"required output {name!r} has sort {actual_sort!r}; expected {output['sort']!r}"
            )
        actual_shape = declaration.get("shape", [])
        if _canonical(actual_shape) != _canonical(output["shape"]):
            diagnostics.append(
                f"required output {name!r} has shape {actual_shape!r}; expected {output['shape']!r}"
            )
    return tuple(diagnostics)


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ModelError(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


_USE_MODEL_JSON_BUDGET = object()


def _read_json(text, *, limit=_USE_MODEL_JSON_BUDGET):
    if limit is _USE_MODEL_JSON_BUDGET:
        from .construction_limits import current_construction_limits
        limit = current_construction_limits().max_model_json_chars
    if not isinstance(text, str) or (limit is not None and len(text) > limit):
        budget = "unbounded" if limit is None else f"{limit // (1024 * 1024)} Mi-character"
        raise ModelError(f"candidate JSON exceeds the {budget} limit")
    return json.loads(
        text,
        object_pairs_hook=_object,
        parse_constant=lambda value: (_ for _ in ()).throw(
            ModelError("nonfinite JSON value")
        ),
    )


def candidate_schema() -> Dict[str, Any]:
    """JSON schema given to proposal providers; compile_model checks semantics."""
    return json.loads(
        resources.files(__package__)
        .joinpath("nl_model.schema.json")
        .read_text(encoding="utf-8")
    )


@dataclass(frozen=True)
class Candidate:
    """Immutable canonical snapshot; model returns a copy, digest covers all data."""

    source: str
    model_json: str
    provider: str
    diagnostics: Tuple[str, ...]
    normalization_json: str = "[]"
    required_outputs_json: str = "[]"
    # None retains the context-managed API. An explicit policy is attached to
    # the candidate independently of subsequent construction contexts.
    size_limits: Optional[CandidateSizeLimits] = None

    @property
    def required_outputs(self):
        return _read_json(self.required_outputs_json, limit=_size_limits(self.size_limits).max_model_json_chars)

    @property
    def model(self):
        return _read_json(self.model_json, limit=_size_limits(self.size_limits).max_model_json_chars)

    @property
    def diagnostic_details(self):
        """Located copies of validation feedback; never an interpretation verdict."""
        return validation_feedback(self.source, self.model, self.diagnostics)

    @property
    def valid(self):
        """No recorded construction errors; target support is checked on compile."""
        return not self.diagnostics

    @property
    def source_sha256(self):
        return _hash(self.source)

    @property
    def digest(self):
        payload = {
            "source": self.source,
            "model": self.model,
            "provider": self.provider,
        }
        ledger = self.normalization_ledger
        if ledger:
            payload["normalization_ledger"] = ledger
        if self.required_outputs:
            payload["required_outputs"] = self.required_outputs
        return _hash(_canonical(payload))

    @property
    def normalization_ledger(self):
        return _read_json(self.normalization_json, limit=_size_limits(self.size_limits).max_model_json_chars)

    def to_json(self):
        envelope = dict(
            schema="somt-nl-candidate-v1",
            source=self.source,
            source_sha256=self.source_sha256,
            model=self.model,
            provider=self.provider,
            digest=self.digest,
        )
        if self.normalization_ledger:
            envelope["normalization_ledger"] = self.normalization_ledger
        if self.required_outputs:
            envelope["required_outputs"] = self.required_outputs
        if self.size_limits is not None and self.size_limits != DEFAULT_CANDIDATE_SIZE_LIMITS:
            envelope["size_limits"] = _size_limits_json(self.size_limits)
        encoded = _canonical(envelope)
        limit = _size_limits(self.size_limits).envelope_limit
        if limit is not None and len(encoded) > limit:
            raise ModelError("candidate envelope exceeds the configured character limit")
        return encoded

    @classmethod
    def from_json(cls, text, *, size_limits=None):
        explicit_size_limits = size_limits is not None
        limits = _size_limits(size_limits)
        envelope = _read_json(text, limit=limits.envelope_limit)
        legacy_fields = {
            "schema",
            "source",
            "source_sha256",
            "model",
            "provider",
            "digest",
        }
        optional_fields = {"required_outputs", "normalization_ledger", "size_limits"}
        if (
            not isinstance(envelope, dict)
            or not legacy_fields <= set(envelope)
            or set(envelope) - legacy_fields - optional_fields
            or envelope["schema"] != "somt-nl-candidate-v1"
        ):
            raise ModelError("invalid candidate envelope")
        if "size_limits" in envelope:
            embedded_limits = _size_limits_from_json(envelope["size_limits"])
            if explicit_size_limits and embedded_limits != size_limits:
                raise ModelError("candidate size_limits metadata conflicts with caller policy")
            if not explicit_size_limits and embedded_limits != DEFAULT_CANDIDATE_SIZE_LIMITS:
                raise ModelError("candidate declares nondefault size_limits; pass them explicitly")
        ledger = envelope.get("normalization_ledger", [])
        required_outputs = _normalize_required_outputs(
            envelope.get("required_outputs")
        )
        payload = {
            "source": envelope["source"],
            "model": envelope["model"],
            "provider": envelope["provider"],
        }
        if ledger:
            payload["normalization_ledger"] = ledger
        if required_outputs:
            payload["required_outputs"] = required_outputs
        if (
            not isinstance(envelope["source"], str)
            or not isinstance(envelope["provider"], str)
            or envelope["source_sha256"] != _hash(envelope["source"])
            or envelope["digest"] != _hash(_canonical(payload))
        ):
            raise ModelError(
                "candidate digest mismatch: source or interpretation changed"
            )
        candidate = _candidate(
            envelope["source"],
            envelope["model"],
            envelope["provider"],
            normalization_ledger=ledger,
            required_outputs=required_outputs,
            size_limits=size_limits,
        )
        if envelope["digest"] != candidate.digest:
            raise ModelError(
                "candidate digest mismatch: source or interpretation changed"
            )
        return candidate


def _candidate(
    source, model, provider, *, normalize_hir=False, normalization_ledger=None,
    required_outputs=None, size_limits=None,
):
    candidate, _ = _prepare_candidate(
        source, model, provider, normalize_hir=normalize_hir,
        normalization_ledger=normalization_ledger,
        required_outputs=required_outputs,
        size_limits=size_limits,
    )
    return candidate


def _prepare_candidate(
    source, model, provider, *, normalize_hir=False, normalization_ledger=None,
    required_outputs=None, size_limits=None, formal_profile="default", formal_dialect=None,
):
    """Validate one snapshot and retain its checked construction for this call.

    Nothing is cached on Candidate: directly constructed snapshots still undergo
    complete validation. HIR lowering happens during compilation. SMT-LIB
    candidates use the native frontend now so syntax/type errors reach repair;
    compilation reuses that result with the requested profile and dialect.
    """
    limits = _size_limits(size_limits)
    source_limit = limits.max_source_chars
    model_limit = limits.max_model_json_chars
    _validate_source_size(source, source_limit)
    if not isinstance(provider, str) or not provider or len(provider) > 256:
        raise ModelError("invalid provider identifier")
    ledger = [] if normalization_ledger is None else normalization_ledger
    if not isinstance(ledger, list) or any(
        not isinstance(item, dict)
        or set(item) != {"path", "rule", "before", "after"}
        or not isinstance(item["path"], str)
        or not isinstance(item["rule"], str)
        for item in ledger
    ):
        raise ModelError("invalid HIR normalization ledger")
    raw_model = model
    if normalize_hir and isinstance(model, dict) and model.get("schema") == HIR_SCHEMA:
        try:
            raw_model, ledger = canonicalize_hir(model)
        except (ValueError, TypeError, KeyError, RecursionError):
            # Keep malformed provider output intact so normal HIR validation
            # can return its ordinary candidate diagnostic.
            raw_model, ledger = model, []
    elif normalization_ledger is not None and ledger:
        # Serialized candidates are immutable snapshots. Never normalize or
        # recanonicalize their model on load or during compilation.
        if not isinstance(model, dict) or model.get("schema") != HIR_SCHEMA:
            raise ModelError("normalization ledger is only valid for an HIR candidate")
    encoded = _canonical(raw_model)
    copied = _read_json(encoded, limit=model_limit)
    encoded_ledger = _canonical(ledger)
    _read_json(encoded_ledger, limit=model_limit)
    diagnostics = ()
    prepared = None
    try:
        if isinstance(copied, dict) and copied.get("schema") == HIR_SCHEMA:
            builder = build_hir(copied, source)
            # build_hir performs complete type/scope/source checks. Eager
            # default lowering here would duplicate the compiler's work and
            # could block a model intended for another exact encoding profile.
            prepared = dict(language="hir", builder=builder, projection={}, domains={})
        elif isinstance(copied, dict) and copied.get("schema") == FORMAL_SCHEMA:
            script, language = validate_formal(
                copied, source, max_program_chars=limits.formal_limit
            )
            prepared = dict(language=language, script=script, projection={}, domains={})
            if language == "smtlib2":
                # Envelope validity alone cannot end a formal-program repair
                # loop. Use structured native diagnostics; parsing never calls
                # a solver. Keep this result only for the current operation.
                from . import OmtDialect, translate
                checked = translate(
                    source=script, language=language, profile=formal_profile,
                    dialect=OmtDialect.Z3 if formal_dialect is None else formal_dialect,
                )
                if not checked.ok:
                    messages = [d.message for d in checked.diagnostic_items]
                    raise ModelError("; ".join(messages or ["SMT-LIB validation failed"]), "program")
                has_objectives = json.loads(checked.report.to_json())["stats"]["num_objectives"] > 0
                if has_objectives != (copied["decision"] == "optimization"):
                    raise ModelError("declared decision and formal objectives disagree", "decision")
                prepared["translation"] = checked
        else:
            script, projection, domains = compile_model(copied, source)
            prepared = dict(language="smtlib2", script=script,
                            projection=projection, domains=domains)
    except (ModelError, ValueError, TypeError, KeyError, RecursionError) as exc:
        diagnostics = (str(exc),)
    normalized_outputs = _normalize_required_outputs(required_outputs)
    if normalized_outputs:
        diagnostics = diagnostics + _required_output_diagnostics(copied, normalized_outputs)
    encoded_outputs = _canonical(normalized_outputs)
    _read_json(encoded_outputs, limit=model_limit)
    return Candidate(source, encoded, provider, diagnostics, encoded_ledger,
                     encoded_outputs, size_limits), prepared


def propose_nl(
    source: str,
    *,
    provider: Optional[Provider] = None,
    language: str = "typed",
    context=None,
    required_outputs=None,
    size_limits=None,
) -> Candidate:
    """Propose a model. Providers are called only when explicitly supplied.

    The provider receives source, source_sha256, JSON schema, and an instruction
    describing the interpretation boundary. It must return the model object.
    Omitted ``size_limits`` uses ``construction_limits`` from the caller's
    context. An explicit ``CandidateSizeLimits`` takes precedence for character
    budgets and remains attached to the candidate. HIR construction budgets
    still come from the context. Provider JSON cannot raise either policy.
    """
    limits = _size_limits(size_limits)
    source_limit = limits.max_source_chars
    model_limit = limits.max_model_json_chars
    _validate_source_size(source, source_limit)
    output_contract = _normalize_required_outputs(required_outputs)
    if required_outputs is not None and language != "hir":
        raise ModelError("required_outputs is supported only for HIR proposals")
    if language != "typed":
        schema = (hir_schema() if language == "hir"
                  else formal_schema(language, max_program_chars=limits.formal_limit))
        # Serialized candidates carry caller-owned context, but providers must
        # return only the model. Advertise the same field boundary we validate.
        schema["properties"].pop("context", None)
        if provider is None:
            raise ModelError("a formal-language proposal requires an explicit provider")
        context = {} if context is None else _read_json(_canonical(context), limit=model_limit)
        if not isinstance(context, dict) or any(
            not isinstance(k, str) or not isinstance(v, str) for k, v in context.items()
        ):
            raise ModelError("context must map names to semantic descriptions")
        context_json = _canonical(context)
        _read_json(context_json, limit=model_limit)
        request = dict(
            source=source,
            source_sha256=_hash(source),
            schema=schema,
            language=language,
            context=context,
            instruction="Return a JSON formal candidate for the selected language. "
            "Use a self-contained model, inline all instance data, no includes, no Python, no solver options. "
            "Preserve constraints, domains, partiality and objectives. "
            "Context is an explicit task convention. Record remaining ambiguities in unresolved. "
            "Link formal fragments to source Unicode code-point spans. "
            "Do not claim intent preservation or optimality.",
        )
        if required_outputs is not None:
            request["required_outputs"] = _read_json(_canonical(output_contract), limit=model_limit)
        if language == "hir":
            request["instruction"] = (
                "Return a native HIR JSON model matching the constructor API. "
                "Do not emit SMT, Python, or a program field. Declare every variable/function, "
                "preserve domains and exact coefficients, attach [start,end] source spans to "
                "constraints/soft_constraints/objectives/goal. Use explicit finite folds for indexed constraints. "
                "Source-defined weighted preferences belong in optional soft_constraints, each with a Bool expr, "
                "positive integer weight string, explicit group (empty string for the default), and span. "
                "Keep mandatory requirements hard. Repeated preferences each contribute their weight; do not split "
                "one preferred conjunction into separately weighted parts. Soft groups follow first appearance, "
                "then explicit objectives; use decision=optimization and lexicographic order for multiple groups/objectives. "
                "Unrestricted quantifiers use forall/exists over open sorts; quantifier=exists_unique requires exactly one simultaneous tuple of its binders satisfying body. "
                "Use uniqueness only when required by the source; valid models may have zero or many solutions. Unknown values to solve for are decision variables, not missing instance parameters. Explicit instance parameters specialize illustrative example sizes, but never silently discard a variant-defining constraint. "
                "For all-different over an entire declared shaped Int array, use the native form {\"op\":\"all_different\",\"args\":[{\"var\":\"name\"}]}; it expands finite arrays row-major. "
                "The CP vector {array,length,prefix} form indexes the last dimension after its fixed prefix; a row needs its preceding fixed indices in prefix. A column or other non-final-axis slice needs an explicit list of indexed scalar expressions. Do not use a whole multidimensional cell count as length without explicit flattening. "
                "Use cp minimum/maximum with a nonempty Int items vector for extrema, and cp element with items, index, and an explicit default for indexed selection. Keep these constructors compact instead of recursively duplicating operands in nested ite expressions. The element default applies outside the items range; retain source-required index bounds rather than inventing a default for an undefined source access. Constrain any named extremum to equal the constructor, including when it is an objective. "
                "For repeated finite counting relations, prefer the supplied compact CP globals instead of expanding every comparison by hand. Use cp global_cardinality over an items vector with exact values/counts (closed=true when the listed categories partition all items); use cp among over an items vector with an explicit finite values list for counts over a subset. For a sliding-window capacity, emit one among relation per valid window and exact source-defined subset. These constructors preserve the complete relation while limiting repeated syntax. Do not omit windows, narrow domains, or add symmetry constraints to reduce construction size. "
                "A function may include binders, an exact body, and a nonempty source span when its definition follows from the source; "
                "otherwise it remains an uninterpreted declaration. Definitions are non-recursive and binders "
                "must match the declared argument sorts. "
                "Use unresolved only for competing readings of the source text that change the model "
                "and are not settled by context; do not use it for absent background facts, unstated "
                "types or identities, or ordinary translation choices. Represent those with declared "
                "uninterpreted individuals and predicates, and assert only what the text or context states. "
                "Context fixes conventions; record remaining source ambiguities in unresolved. "
                "When an auxiliary variable represents a source-defined quantity or objective (for example, "
                "total cost or maximum completion time), constrain it to equal its exact definition over the "
                "decision variables. Do not use only a one-sided bound merely because optimization would force "
                "equality at an optimum: preserve the full feasible decision/cost relation. "
                "Keep the decision fields consistent: satisfiability has no objectives or soft constraints and goal is null; "
                "optimization has at least one objective or soft constraint and goal is null; validity has a goal "
                "and no objectives or soft constraints. "
                "Always provide objective_order as the schema value single or lexicographic, even when there are "
                "no objectives. Never add a dummy objective just to fill that required field. "
                "Before returning, check every source requirement has a constraint or objective, "
                "inequality directions, units, quantifier scope, and objective meaning."
                + _HIR_COVERAGE_GUIDANCE
                + (" The caller supplied required_outputs; declare each exact name, sort, "
                   "and shape in the top-level declarations. Do not rename, omit, resize, "
                   "transpose, or coerce any required output. These entries are an API contract, "
                   "not permission to add constraints or infer semantics."
                   if required_outputs is not None else "")
                + _HIR_CONSTRUCTOR_GUIDANCE
                + " " + MODELING_GUIDANCE
            )
        if language == "minizinc":
            request["instruction"] += (
                " This frontend supports finite generator folds such as sum(i in 1..n)(x[i]); "
                "use that form instead of sum(x). Inline finite data using scalar parameters "
                "or explicit constraints when richer parameter arrays are unsupported."
            )
        request["instruction"] += (
            " The context belongs to the caller's request envelope. Use its conventions "
            "when constructing the model, but do not return a context field."
        )
        request["instruction"] += _SOURCE_RELATION_GUIDANCE
        proposed = provider(request)
        if (
            not isinstance(proposed, dict)
            or proposed.get("language") != language
            or proposed.get("schema")
            != (HIR_SCHEMA if language == "hir" else FORMAL_SCHEMA)
            or "context" in proposed
        ):
            raise ModelError("provider changed the requested language configuration")
        proposed = dict(proposed, context=_read_json(context_json, limit=model_limit))
        provider_name = getattr(provider, "__name__", type(provider).__name__)
        return _candidate(
            source,
            proposed,
            "external:" + provider_name,
            normalize_hir=(language == "hir"),
            required_outputs=output_contract,
            size_limits=size_limits,
        )
    if context is not None:
        raise ModelError("explicit context requires a formal-language configuration")
    if provider is None:
        return _candidate(source, propose_controlled(source, max_source_chars=source_limit),
                          "controlled-en-zh-v1", size_limits=size_limits)
    request = dict(
        source=source,
        source_sha256=_hash(source),
        schema=candidate_schema(),
        instruction="Return a typed model matching schema. Preserve every requested constraint. "
        "Record assumptions and unresolved alternatives. Use exact source character spans. "
        "Do not resolve ambiguous decisions, domains, quantifier scope or objective order silently. "
        "No executable code or raw SMT is accepted.",
    )
    request["instruction"] += _SOURCE_RELATION_GUIDANCE
    proposed = provider(request)
    provider_name = getattr(provider, "__name__", type(provider).__name__)
    return _candidate(source, proposed, "external:" + provider_name,
                      size_limits=size_limits)


@dataclass(frozen=True)
class ProposalTrace:
    """Ordered immutable proposals; validity covers construction, not intent."""

    attempts: Tuple[Candidate, ...]

    @property
    def candidate(self) -> Candidate:
        return self.attempts[-1]

    @property
    def stop_reason(self) -> str:
        return "valid-candidate" if self.candidate.valid else "attempt-limit"


def propose_nl_with_repair(
    source: str,
    *,
    provider: Provider,
    max_attempts: int = 1,
    language: str = "hir",
    context=None,
    required_outputs=None,
    size_limits=None,
) -> ProposalTrace:
    """Request up to max_attempts candidates using local validation feedback.

    Every request retains the source, schema and caller's context. Later requests
    additionally receive the previous immutable model, digest and diagnostics in
    ``repair``. No reference model or solver verdict is used. Stop at the first
    valid candidate; provider/service exceptions propagate without retries.
    Compilation still requires explicit selection of a candidate's digest.
    ``size_limits`` is passed unchanged through every proposal attempt.
    """
    if type(max_attempts) is not int or max_attempts < 1:
        raise ModelError("max_attempts must be a positive integer")
    if not callable(provider):
        raise ModelError("repair proposals require an explicit callable provider")
    limits = _size_limits(size_limits)
    fixed_context = None if context is None else _read_json(
        _canonical(context), limit=limits.max_model_json_chars
    )
    fixed_required_outputs = _normalize_required_outputs(required_outputs)
    if required_outputs is not None and language != "hir":
        raise ModelError("required_outputs is supported only for HIR proposals")
    attempts = []

    def request_provider(request):
        if attempts:
            previous = attempts[-1]
            previous_model = previous.model
            if language != "typed":
                # Context belongs to the caller's envelope, not the provider's
                # response schema. Return a model the provider can copy/edit.
                previous_model.pop("context", None)
            request["repair"] = dict(
                attempt=len(attempts) + 1,
                previous_candidate=previous_model,
                previous_digest=previous.digest,
                diagnostics=list(previous.diagnostics),
                diagnostic_details=previous.diagnostic_details,
                instruction="Return a complete replacement candidate correcting the reported "
                "construction errors. Preserve the original source requirements and fixed "
                "context, including domains, constraints and objectives. Do not delete a "
                "requirement to pass validation or silently settle a source ambiguity. "
                "Diagnostics include JSON paths: preserve and use each path to locate the malformed "
                "field, then repair its type or structure using only the source and fixed context. "
                "Do not infer missing constants, constraints, or intended meanings from the error, "
                "and do not consult reference models or solver answers. "
                "The diagnostics establish no intended interpretation or solver answer. If a diagnostic reports HIR construction-budget or CP-expansion size, preserve every source clause and refactor repeated exact finite count/window relations to compact listed CP constructors (such as global_cardinality or among) only when their documented semantics match; include every required value, count, valid window and source-defined capacity. Never reduce size by dropping constraints, bounds or observables.",
            )
            if language == "hir":
                request["repair"]["instruction"] += (
                    " diagnostic_details supplies validator paths and JSON pointers; a source excerpt comes only from the previous candidate's own span annotation and does not prove source alignment. "
                    "An unresolved_interpretation diagnostic locates an existing alternative; it does not authorize removing it. Review each item against the source and fixed context: state the competing readings and their exact ambiguous phrase, or explain why the entry is only an encoding note. Preserve any genuine unresolved alternative. Never move one into interpretation_notes or assumptions merely to make validation pass. "
                    " For all-different over a whole shaped Int array, use native HIR all_different on the array or explicit scalar cells; "
                    "a CP vector descriptor indexes only its final axis, so never set length to the total cell count of a multidimensional array. "
                    "For CP table, consult the schema and supply the required positive Boolean from the source: true for allowed tuples, false for forbidden tuples. "
                    "Before responding, audit each source domain, data row, independent constraint, objective and requested observable against the replacement model; "
                    "do not leave requirements out to pass validation. Preserve genuine source conflicts in unresolved."
                )
                if fixed_required_outputs:
                    request["repair"]["instruction"] += (
                        " The caller-supplied required_outputs list is a fixed API contract; "
                        "preserve every listed name, sort, and shape exactly."
                    )
        return provider(request)

    # Keep provenance tied to the actual provider, rather than this adapter.
    request_provider.__name__ = getattr(provider, "__name__", type(provider).__name__)
    for _ in range(max_attempts):
        candidate = propose_nl(source, provider=request_provider, language=language,
                               context=fixed_context,
                               required_outputs=(fixed_required_outputs
                                                 if required_outputs is not None else None),
                               size_limits=size_limits)
        attempts.append(candidate)
        if candidate.valid:
            break
    return ProposalTrace(tuple(attempts))


@dataclass(frozen=True)
class NaturalLanguageTranslation:
    candidate: Candidate
    translation: Any
    diagnostics: Tuple[str, ...]
    acceptance: str
    _projection_json: str = "{}"
    _domains_json: str = "{}"
    _dialect: Any = None

    @property
    def ok(self):
        return (
            self.translation is not None
            and self.translation.ok
            and not self.diagnostics
        )

    def to_smt2(self):
        if not self.ok:
            raise ModelError("translation unavailable: " + "; ".join(self.diagnostics))
        return self.translation.to_smt2(dialect=self._dialect)

    def report(self):
        formal = (
            json.loads(self.translation.report.to_json())
            if self.translation is not None
            else None
        )
        model = self.candidate.model
        if not isinstance(model, dict):
            model = {}
        return dict(
            schema="somt-nl-report-v1",
            source_sha256=self.candidate.source_sha256,
            candidate_digest=self.candidate.digest,
            provider=self.candidate.provider,
            interpretation=self.acceptance,
            intent_preservation="not-proved",
            guarantee_scope="selected formal interpretation",
            decision=model.get("decision"),
            verdict_polarity="invert"
            if model.get("decision") == "validity"
            else "preserve",
            assumptions=model.get("assumptions", []),
            interpretation_notes=model.get("interpretation_notes", []),
            normalization_ledger=self.candidate.normalization_ledger,
            diagnostics=list(self.diagnostics),
            observables=json.loads(self._projection_json),
            source_links={
                key: model.get(key)
                for key in ["domains", "symbols", "constraints", "soft_constraints", "functions", "objectives", "goal"]
                if key != "soft_constraints" or key in model
            },
            language_configuration=model.get("language", "typed"),
            context=model.get("context", {}),
            formal_source_links=model.get("links", []),
            formal_translation=formal,
        )

    def interpret_solver_answer(self, answer):
        """Interpret one conclusive answer; SAT alone never proves optimality."""
        if not self.ok or answer not in ["sat", "unsat", "unknown"]:
            raise ModelError("expected a successful translation and sat/unsat/unknown")
        fidelity = self.translation.report.fidelity
        trusted = (
            (answer == "sat" and fidelity.sound)
            or (answer == "unsat" and fidelity.complete)
        ) and not fidelity.bounds
        decision = self.candidate.model["decision"]
        status = "unknown"
        if trusted:
            status = (
                {"sat": "invalid", "unsat": "valid"}
                if decision == "validity"
                else {"sat": "feasible", "unsat": "infeasible"}
            )[answer]
        return dict(
            decision=decision,
            status=status,
            scope="selected formal interpretation",
            optimality="not-established",
        )

    def project_assignment(self, assignment):
        """Decode exact scalar values; this is not a source constraint replay.

        Supply Python bool/int/Fraction (or exact rational strings for Real).
        Predicate interpretations are not decoded by this scalar interface.
        """
        if not self.ok:
            raise ModelError("cannot project an unsuccessful translation")
        if self.candidate.model.get("schema") in [FORMAL_SCHEMA, HIR_SCHEMA]:
            raise ModelError(
                "this formal configuration has no checked NL observable projection; use a dataset witness checker"
            )
        domains = json.loads(self._domains_json)
        source = {}
        for n, spec in json.loads(self._projection_json).items():
            if spec["target"] not in assignment:
                raise ModelError(f"missing observable {spec['target']}")
            v = assignment[spec["target"]]
            sort = spec["sort"]
            if sort == "Bool":
                if type(v) is not bool:
                    raise ModelError(f"{n} requires an exact Boolean")
            elif sort == "Int" or sort in domains:
                if type(v) is not int:
                    raise ModelError(f"{n} requires an exact integer")
                if sort in domains:
                    if not 0 <= v < len(domains[sort]):
                        raise ModelError(f"{n} is outside the source domain")
                    v = domains[sort][v]
            else:
                if type(v) not in [int, str, Fraction]:
                    raise ModelError(f"{n} requires an exact rational, not a float")
                v = Fraction(v)
            source[n] = v
        return source

    def replay_assignment(self, assignment):
        """Replay exact source-level values against every source constraint.

        The assignment maps source symbol names to exact values -- the shape
        `project_assignment` returns, with finite-domain members decoded to
        their names. The values are substituted into the candidate's own ASTs
        under the same relational semantics the compiler encodes (rational
        arithmetic, definedness guards, short-circuit `ite`, finite-domain
        quantifiers), so a wrong encoding or projection cannot validate
        itself. Constraints whose expressions apply a predicate are refused:
        a predicate's witness is an interpretation this replay does not
        decode. The report is factual -- `{holds, violations, goal,
        objectives}`; interpreting validity polarity or optimality stays with
        the caller.
        """
        if not self.ok:
            raise ModelError("cannot replay against an unsuccessful translation")
        if self.candidate.model.get("schema") in [FORMAL_SCHEMA, HIR_SCHEMA]:
            raise ModelError(
                "this formal configuration has no checked NL replay; use a dataset witness checker"
            )
        from ._nl_model import replay_model

        return replay_model(
            self.candidate.model, self.candidate.source, assignment
        )


def _compile(candidate, acceptance, profile, dialect):
    # Revalidate snapshots, including ones constructed directly by API callers.
    candidate, prepared = _prepare_candidate(
        candidate.source,
        candidate.model,
        candidate.provider,
        normalization_ledger=candidate.normalization_ledger,
        required_outputs=candidate.required_outputs,
        formal_profile=profile, formal_dialect=dialect,
        size_limits=candidate.size_limits,
    )
    if candidate.diagnostics:
        return NaturalLanguageTranslation(
            candidate, None, candidate.diagnostics, "unresolved"
        )
    language = prepared["language"]
    projection, domains = prepared["projection"], prepared["domains"]
    from . import OmtDialect, translate

    if dialect is None:
        dialect = OmtDialect.Z3
    if language == "hir":
        translation = prepared["builder"].translate(profile=profile, dialect=dialect)
    elif "translation" in prepared:
        translation = prepared["translation"]
    else:
        translation = translate(
            source=prepared["script"], language=language, profile=profile, dialect=dialect
        )
    diagnostics = (
        tuple(d.message for d in translation.diagnostic_items) if not translation.ok else ()
    )
    if translation.ok:
        has_objectives = (
            json.loads(translation.report.to_json())["stats"]["num_objectives"] > 0
        )
        if has_objectives != (candidate.model["decision"] == "optimization"):
            diagnostics = ("declared decision and formal objectives disagree",)
    return NaturalLanguageTranslation(
        candidate,
        translation,
        diagnostics,
        acceptance,
        _canonical(projection),
        _canonical(domains),
        dialect,
    )


def compile_candidate(
    candidate: Candidate,
    *,
    accept_digest: str = "",
    profile: str = "default",
    dialect=None,
) -> NaturalLanguageTranslation:
    """Compile only the exact explicitly selected interpretation.

    The digest binds selection to content; it is not a signature or an intent
    correctness proof. It must change when the source or candidate changes.
    """
    if accept_digest != candidate.digest:
        return NaturalLanguageTranslation(
            candidate,
            None,
            ("interpretation selection required: pass this candidate's exact digest",),
            "pending",
        )
    return _compile(candidate, "explicit-selection", profile, dialect)


def translate_nl(
    source: str,
    *,
    provider: Optional[Provider] = None,
    accept_digest: str = "",
    profile: str = "default",
    dialect=None,
    size_limits=None,
):
    """Translate controlled text directly, or propose a provider interpretation.

    For external providers prefer propose_nl followed by compile_candidate, so
    review does not rerun a nondeterministic proposal. The built-in grammar is
    an explicit interpretation rule, not general unrestricted NL understanding.
    """
    candidate = propose_nl(source, provider=provider, size_limits=size_limits)
    if provider is None:
        return _compile(candidate, "controlled-grammar-v1", profile, dialect)
    return compile_candidate(
        candidate, accept_digest=accept_digest, profile=profile, dialect=dialect
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command in ["propose", "translate", "compile"]:
        p = sub.add_parser(command)
        p.add_argument("file", help="UTF-8 source text, or candidate JSON for compile")
        if command == "compile":
            p.add_argument("--accept-digest", required=True)
        if command == "propose":
            p.add_argument(
                "--provider", choices=["controlled", "deepseek"], default="controlled"
            )
            p.add_argument("--model", help="DeepSeek model (or DEEPSEEK_MODEL)")
            p.add_argument(
                "--language",
                choices=["typed", "hir", "minizinc", "lp", "xcsp3", "smtlib2"],
                default="typed",
            )
            p.add_argument(
                "--context", type=Path, help="JSON map of task semantic conventions"
            )
        if command != "propose":
            p.add_argument("--profile", default="default")
            p.add_argument(
                "--dialect",
                choices=["z3", "smtlib-omt-2025", "optimathsat", "none"],
                default="z3",
            )
            p.add_argument("--report", type=Path)
    args = parser.parse_args(argv)
    try:
        raw = Path(args.file).read_text(encoding="utf-8")
        if args.command == "propose":
            provider = None
            if args.provider == "deepseek":
                from .deepseek import DeepSeekProvider

                provider = DeepSeekProvider(model=args.model)
            elif args.model:
                raise ModelError("--model requires --provider deepseek")
            context = (
                _read_json(args.context.read_text(encoding="utf-8"))
                if args.context
                else None
            )
            c = propose_nl(
                raw, provider=provider, language=args.language, context=context
            )
            print(c.to_json())
            for diagnostic in c.diagnostics:
                print(diagnostic, file=sys.stderr)
            return 0 if c.valid else 1
        from . import OmtDialect

        dialect = {
            "z3": OmtDialect.Z3,
            "smtlib-omt-2025": OmtDialect.SmtLib2025,
            "optimathsat": OmtDialect.OptiMathSAT,
            "none": OmtDialect.NONE,
        }[args.dialect]
        result = (
            compile_candidate(
                Candidate.from_json(raw),
                accept_digest=args.accept_digest,
                profile=args.profile,
                dialect=dialect,
            )
            if args.command == "compile"
            else translate_nl(raw, profile=args.profile, dialect=dialect)
        )
        if args.report:
            if args.report.resolve() == Path(args.file).resolve():
                raise ModelError(
                    "report path must not overwrite source/candidate input"
                )
            args.report.write_text(
                json.dumps(result.report(), ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
        if not result.ok:
            for diagnostic in result.diagnostics:
                print(diagnostic, file=sys.stderr)
            return 1
        print(result.to_smt2(), end="")
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
