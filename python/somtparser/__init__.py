"""SOMTParser: Python bindings for the SOMTParser SMT-LIB2 / OMT front-end library.

Parse SMT-LIB2 and OMT input into a typed DAG IR, build expressions
programmatically, convert formulas (NNF/CNF/DNF), parse solver models and
evaluate formulas under (partial) models.

Example:
    >>> import somtparser as sp
    >>> p = sp.parse("(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))")
    >>> len(p.assertions)
    1
    >>> m = p.parse_model("(model (define-fun x () Int 3))")
    >>> p.evaluate(p.assertions[0], m).value
    True
"""

import os
import sys

if sys.platform == "win32":
    _package_dir = os.path.dirname(os.path.abspath(__file__))
    _bin_dir = os.path.join(_package_dir, "bin")
    if os.path.isdir(_bin_dir):
        os.add_dll_directory(_bin_dir)
        os.environ["PATH"] = _bin_dir + os.pathsep + os.environ.get("PATH", "")

from ._somtparser import (
    __version__,
    CmdType,
    Command,
    MetaObjective,
    Model,
    Node,
    Objective,
    OptKind,
    ParseError,
    Parser,
    ResultType,
    Script,
    Sort,
    parse,
    parse_file,
)

__all__ = [
    "CmdType",
    "Command",
    "MetaObjective",
    "Model",
    "Node",
    "Objective",
    "OptKind",
    "ParseError",
    "Parser",
    "ResultType",
    "Script",
    "Sort",
    "parse",
    "parse_file",
    "__version__",
]
