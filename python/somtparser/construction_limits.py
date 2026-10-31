"""Caller-owned construction budgets, independent of a model's semantics.

Use ``construction_limits(max_hir_nodes=None, max_source_chars=None,
max_finite_elements=None, max_model_json_chars=None, max_formal_program_chars=131072,
max_envelope_json_chars=None)`` for a
trusted large input. Defaults remain bounded. Limits are local to a thread or
async task and are never read from provider-generated JSON. A builder snapshots
its node budget; deserialize/propose/compile inside the chosen context.
"""
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, replace
from typing import Optional


@dataclass(frozen=True)
class ConstructionLimits:
    max_hir_nodes: Optional[int] = 100000
    max_source_chars: Optional[int] = 131072
    max_finite_elements: Optional[int] = 10000
    max_model_json_chars: Optional[int] = 16 * 1024 * 1024
    max_formal_program_chars: Optional[int] = 131072
    max_envelope_json_chars: Optional[int] = 48 * 1024 * 1024

    def __post_init__(self):
        for name in ("max_hir_nodes", "max_source_chars", "max_finite_elements",
                     "max_model_json_chars", "max_formal_program_chars",
                     "max_envelope_json_chars"):
            value = getattr(self, name)
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError(name + " must be a positive integer or None")


_CURRENT = ContextVar("somt_construction_limits", default=ConstructionLimits())
_UNSET = object()


def current_construction_limits():
    return _CURRENT.get()


@contextmanager
def construction_limits(*, max_hir_nodes=_UNSET, max_source_chars=_UNSET,
                        max_finite_elements=_UNSET, max_model_json_chars=_UNSET,
                        max_formal_program_chars=_UNSET, max_envelope_json_chars=_UNSET):
    changes = {name: value for name, value in (
        ("max_hir_nodes", max_hir_nodes), ("max_source_chars", max_source_chars),
        ("max_finite_elements", max_finite_elements),
        ("max_model_json_chars", max_model_json_chars),
        ("max_formal_program_chars", max_formal_program_chars),
        ("max_envelope_json_chars", max_envelope_json_chars))
        if value is not _UNSET}
    limits = replace(_CURRENT.get(), **changes)
    token = _CURRENT.set(limits)
    try:
        yield limits
    finally:
        _CURRENT.reset(token)
