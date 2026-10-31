/**
 * Python bindings for SOMTParser using pybind11.
 *
 * Design notes (safety first):
 *  - Every object handed to Python is held by std::shared_ptr. DAGNode owns its
 *    whole subtree (children / sort / value are shared_ptr), so nodes stay valid
 *    even after the originating Parser is garbage-collected.
 *  - C++ ParseErrorException is translated to somtparser.ParseError.
 *  - Builder methods that return NT_ERROR / null nodes raise ValueError instead
 *    of leaking broken nodes into Python code.
 *  - Python ints are converted through strings (GMP-backed on the C++ side), so
 *    arbitrary-precision constants are preserved exactly.
 */

#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include <somtparser/parser.h>

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace py = pybind11;
using namespace SOMTParser;

using NodePtr  = std::shared_ptr<DAGNode>;
using SortPtr  = std::shared_ptr<Sort>;
using ModelPtr = std::shared_ptr<Model>;

namespace {

/** ParseError subclass carrying a custom message. */
struct BindParseError : ParseErrorException {
    std::string msg;
    explicit BindParseError(std::string m) : msg(std::move(m)) {}
    const char* what() const noexcept override { return msg.c_str(); }
};

/** Raise ValueError when a builder returned a null / error node. */
NodePtr checked(NodePtr n, const char* ctx) {
    if (!n) {
        throw py::value_error(std::string(ctx) + ": operation returned no node");
    }
    if (n->isErr()) {
        throw py::value_error(std::string(ctx) + ": " + n->getName());
    }
    return n;
}

/** Raise ValueError when two BV operands have different widths. The C++
 *  builders only check "is a bitvector", so a mismatch would silently
 *  produce an ill-sorted node. */
void check_bv_same_width(const NodePtr& a, const NodePtr& b, const char* ctx) {
    if (a && b && a->getSort() && b->getSort() &&
        a->getSort()->isBv() && b->getSort()->isBv()) {
        const size_t wa = a->getSort()->getBitWidth();
        const size_t wb = b->getSort()->getBitWidth();
        if (wa != wb) {
            throw py::value_error(std::string(ctx) + ": bit-width mismatch (" +
                                  std::to_string(wa) + " vs " + std::to_string(wb) + ")");
        }
    }
}

/** SMT-LIB requires (_ BitVec m) with m >= 1. */
void check_bv_width_positive(size_t width, const char* ctx) {
    if (width < 1) {
        throw py::value_error(std::string(ctx) + ": bit-vector width must be >= 1");
    }
}

/** Size of dumpSMTLIB2(root) computed in O(|DAG|) with memoization,
 *  saturating at `cap`. The text expansion of a shared DAG is exponential
 *  in its depth, so __repr__ must know the size BEFORE dumping. */
size_t dump_size_estimate(const NodePtr& root, size_t cap) {
    if (!root) return 0;
    std::unordered_map<const DAGNode*, size_t> memo;
    std::vector<const DAGNode*> stack{root.get()};
    while (!stack.empty()) {
        const DAGNode* cur = stack.back();
        if (memo.count(cur)) { stack.pop_back(); continue; }
        bool ready = true;
        size_t total = cur->getName().size() + 4;  // name + parens/spaces slack
        for (const auto& ch : cur->getChildren()) {
            if (!ch) continue;
            auto it = memo.find(ch.get());
            if (it == memo.end()) {
                stack.push_back(ch.get());
                ready = false;
            } else {
                total += it->second + 1;
            }
        }
        if (ready) {
            memo[cur] = total > cap ? cap : total;
            stack.pop_back();
        }
    }
    return memo[root.get()];
}

/** nullptr → None for optional node fields. */
py::object opt_node(const NodePtr& n) {
    if (!n || n->isNull()) return py::none();
    return py::cast(n);
}

py::object opt_sort(const SortPtr& s) {
    if (!s) return py::none();
    return py::cast(s);
}

/** Convert a Python int (arbitrary precision) or str to a decimal string. */
std::string int_like_to_string(const py::object& v, const char* ctx) {
    if (py::isinstance<py::int_>(v) || py::isinstance<py::str>(v)) {
        return py::str(v).cast<std::string>();
    }
    throw py::type_error(std::string(ctx) + ": expected int or str");
}

/** Extract a Python value from a constant node (None when not a constant). */
py::object node_value(const DAGNode& n) {
    try {
        if (n.isTrue())  return py::bool_(true);
        if (n.isFalse()) return py::bool_(false);
        if (!n.isConst()) return py::none();
        const std::string name = n.getName();
        if (n.isCStr() && n.getSort() && n.getSort()->isStr()) {
            return py::str(n.getStringLiteral());
        }
        if (n.isCBV()) {
            if (name.size() > 2 && name[0] == '#' && name[1] == 'b') {
                return py::int_(py::module_::import("builtins").attr("int")(
                    py::str(name.substr(2)), 2));
            }
            if (name.size() > 2 && name[0] == '#' && name[1] == 'x') {
                return py::int_(py::module_::import("builtins").attr("int")(
                    py::str(name.substr(2)), 16));
            }
            return py::str(name);
        }
        if (n.isCInt() && n.getSort() && (n.getSort()->isInt() || n.getSort()->isIntOrReal())
            && name.find('.') == std::string::npos && name.find('/') == std::string::npos) {
            return py::int_(py::str(name));
        }
        if (n.isCReal() || n.isCInt()) {
            if (name.find('/') != std::string::npos) {
                return py::module_::import("fractions").attr("Fraction")(py::str(name));
            }
            return py::float_(py::float_(py::str(name)));
        }
        return py::str(name);
    } catch (const py::error_already_set&) {
        // Fall back to the raw literal if numeric conversion fails.
        return py::str(n.getName());
    }
}

std::vector<NodePtr> set_to_vector(const std::unordered_set<NodePtr>& s) {
    return std::vector<NodePtr>(s.begin(), s.end());
}

} // namespace

PYBIND11_MODULE(_somtparser, m) {
    m.doc() = "SOMTParser: SMT-LIB2 / OMT parser library - Python bindings";

    // ===== Exceptions =====
    // Translates both ParseErrorException and BindParseError (subclass).
    py::register_exception<ParseErrorException>(m, "ParseError");

    // ===== Enums =====
    py::enum_<RESULT_TYPE>(m, "ResultType", "Result recorded while parsing (e.g. after (check-sat))")
        .value("SAT", RESULT_TYPE::RT_SAT)
        .value("UNSAT", RESULT_TYPE::RT_UNSAT)
        .value("DELTA_SAT", RESULT_TYPE::RT_DELTA_SAT)
        .value("UNKNOWN", RESULT_TYPE::RT_UNKNOWN)
        .value("ERROR", RESULT_TYPE::RT_ERROR);

    py::enum_<OPT_KIND>(m, "OptKind", "Optimization objective kind")
        .value("MINIMIZE", OPT_KIND::OPT_MINIMIZE)
        .value("MAXIMIZE", OPT_KIND::OPT_MAXIMIZE)
        .value("MAXSAT", OPT_KIND::OPT_MAXSAT)
        .value("MINSAT", OPT_KIND::OPT_MINSAT)
        .value("LEX", OPT_KIND::OPT_LEX_OPTIMIZE)
        .value("PARETO", OPT_KIND::OPT_PARETO_OPTIMIZE)
        .value("BOX", OPT_KIND::OPT_BOX_OPTIMIZE)
        .value("MINMAX", OPT_KIND::OPT_MINMAX)
        .value("MAXMIN", OPT_KIND::OPT_MAXMIN)
        .value("NONE", OPT_KIND::OPT_NULL)
        .export_values();

    py::enum_<CMD_TYPE>(m, "CmdType", "SMT-LIB command type (Script entries)")
        .value("UNKNOWN", CMD_TYPE::CT_UNKNOWN)
        .value("EOF", CMD_TYPE::CT_EOF)
        .value("ASSERT", CMD_TYPE::CT_ASSERT)
        .value("CHECK_SAT", CMD_TYPE::CT_CHECK_SAT)
        .value("CHECK_SAT_ASSUMING", CMD_TYPE::CT_CHECK_SAT_ASSUMING)
        .value("DECLARE_CONST", CMD_TYPE::CT_DECLARE_CONST)
        .value("DECLARE_FUN", CMD_TYPE::CT_DECLARE_FUN)
        .value("DECLARE_SORT", CMD_TYPE::CT_DECLARE_SORT)
        .value("DECLARE_DATATYPES", CMD_TYPE::CT_DECLARE_DATATYPES)
        .value("DECLARE_CODATATYPES", CMD_TYPE::CT_DECLARE_CODATATYPES)
        .value("DEFINE_FUN", CMD_TYPE::CT_DEFINE_FUN)
        .value("DEFINE_FUN_REC", CMD_TYPE::CT_DEFINE_FUN_REC)
        .value("DEFINE_FUNS_REC", CMD_TYPE::CT_DEFINE_FUNS_REC)
        .value("DEFINE_SORT", CMD_TYPE::CT_DEFINE_SORT)
        .value("ECHO", CMD_TYPE::CT_ECHO)
        .value("EXIT", CMD_TYPE::CT_EXIT)
        .value("GET_ASSERTIONS", CMD_TYPE::CT_GET_ASSERTIONS)
        .value("GET_ASSIGNMENT", CMD_TYPE::CT_GET_ASSIGNMENT)
        .value("GET_INFO", CMD_TYPE::CT_GET_INFO)
        .value("GET_MODEL", CMD_TYPE::CT_GET_MODEL)
        .value("GET_OPTION", CMD_TYPE::CT_GET_OPTION)
        .value("GET_PROOF", CMD_TYPE::CT_GET_PROOF)
        .value("GET_UNSAT_ASSUMPTIONS", CMD_TYPE::CT_GET_UNSAT_ASSUMPTIONS)
        .value("GET_UNSAT_CORE", CMD_TYPE::CT_GET_UNSAT_CORE)
        .value("GET_VALUE", CMD_TYPE::CT_GET_VALUE)
        .value("POP", CMD_TYPE::CT_POP)
        .value("PUSH", CMD_TYPE::CT_PUSH)
        .value("RESET", CMD_TYPE::CT_RESET)
        .value("RESET_ASSERTIONS", CMD_TYPE::CT_RESET_ASSERTIONS)
        .value("SET_INFO", CMD_TYPE::CT_SET_INFO)
        .value("SET_LOGIC", CMD_TYPE::CT_SET_LOGIC)
        .value("SET_OPTION", CMD_TYPE::CT_SET_OPTION)
        .value("EXISTS", CMD_TYPE::CT_EXISTS)
        .value("FORALL", CMD_TYPE::CT_FORALL)
        .value("GET_OBJECTIVES", CMD_TYPE::CT_GET_OBJECTIVES)
        .value("ASSERT_SOFT", CMD_TYPE::CT_ASSERT_SOFT)
        .value("DEFINE_OBJ", CMD_TYPE::CT_DEFINE_OBJ)
        .value("DEFINE_MIN_OBJ", CMD_TYPE::CT_DEFINE_MIN_OBJ)
        .value("DEFINE_MAX_OBJ", CMD_TYPE::CT_DEFINE_MAX_OBJ)
        .value("MINIMIZE", CMD_TYPE::CT_MINIMIZE)
        .value("MAXIMIZE", CMD_TYPE::CT_MAXIMIZE)
        .value("LEX_OPTIMIZE", CMD_TYPE::CT_LEX_OPTIMIZE)
        .value("PARETO_OPTIMIZE", CMD_TYPE::CT_PARETO_OPTIMIZE)
        .value("BOX_OPTIMIZE", CMD_TYPE::CT_BOX_OPTIMIZE)
        .value("MINMAX", CMD_TYPE::CT_MINMAX)
        .value("MAXMIN", CMD_TYPE::CT_MAXMIN)
        .value("MAXSAT", CMD_TYPE::CT_MAXSAT)
        .value("MINSAT", CMD_TYPE::CT_MINSAT)
        .value("OPTIMIZE", CMD_TYPE::CT_OPTIMIZE);

    // ===== Sort =====
    py::class_<Sort, SortPtr>(m, "Sort", "SMT-LIB2 sort (type)")
        .def_property_readonly("name", [](const Sort& s) { return s.name; })
        .def_property_readonly("arity", [](const Sort& s) { return s.arity; })
        .def_property_readonly("is_bool", &Sort::isBool)
        .def_property_readonly("is_int", &Sort::isInt)
        .def_property_readonly("is_real", &Sort::isReal)
        .def_property_readonly("is_int_or_real", &Sort::isIntOrReal)
        .def_property_readonly("is_bv", &Sort::isBv)
        .def_property_readonly("is_fp", &Sort::isFp)
        .def_property_readonly("is_string", &Sort::isStr)
        .def_property_readonly("is_regex", &Sort::isReg)
        .def_property_readonly("is_array", &Sort::isArray)
        .def_property_readonly("is_datatype", &Sort::isDatatype)
        .def_property_readonly("is_rounding_mode", &Sort::isRoundingMode)
        .def_property_readonly("is_uninterpreted", &Sort::isDec)
        .def_property_readonly("bv_width", &Sort::getBitWidth,
            "BitVec width (0 if not a BV sort)")
        .def_property_readonly("fp_exponent_width", &Sort::getExponentWidth,
            "FloatingPoint exponent width (0 if not an FP sort)")
        .def_property_readonly("fp_significand_width", &Sort::getSignificandWidth,
            "FloatingPoint significand width (0 if not an FP sort)")
        .def_property_readonly("index_sort", [](const Sort& s) {
            return s.isArray() ? opt_sort(s.getIndexSort()) : py::none();
        }, "Array index sort (None if not an array sort)")
        .def_property_readonly("elem_sort", [](const Sort& s) {
            return s.isArray() ? opt_sort(s.getElemSort()) : py::none();
        }, "Array element sort (None if not an array sort)")
        .def("__eq__", [](const Sort& a, const Sort& b) { return a.isEqTo(b); },
            py::is_operator())
        .def("__ne__", [](const Sort& a, const Sort& b) { return !a.isEqTo(b); },
            py::is_operator())
        .def("__hash__", &Sort::hash)
        .def("__str__", &Sort::toString)
        .def("__repr__", [](const Sort& s) { return "<Sort " + s.toString() + ">"; });

    // ===== Node =====
    py::class_<DAGNode, NodePtr>(m, "Node", "Typed DAG expression node")
        .def_property_readonly("kind", [](const DAGNode& n) {
            return kindToString(n.getKind());
        }, "Node kind as string (e.g. 'and', 'add', 'var')")
        .def_property_readonly("sort", &DAGNode::getSort)
        .def_property_readonly("name", &DAGNode::getName,
            "Symbol name (variables) or literal text (constants)")
        .def_property_readonly("value", [](const DAGNode& n) { return node_value(n); },
            "Python value for constants (bool/int/float/Fraction/str), None otherwise")
        .def_property_readonly("num_children", &DAGNode::getChildrenSize)
        .def_property_readonly("children", &DAGNode::getChildren)
        .def_property_readonly("bit_width", &DAGNode::getBitWidth,
            "BV width of this node's sort (0 if not BV)")

        // Category checks
        .def_property_readonly("is_const", &DAGNode::isConst)
        .def_property_readonly("is_var", &DAGNode::isVar)
        .def_property_readonly("is_leaf", &DAGNode::isLeaf)
        .def_property_readonly("is_internal", &DAGNode::isInternal)
        .def_property_readonly("is_err", &DAGNode::isErr)
        .def_property_readonly("is_null", &DAGNode::isNull)
        .def_property_readonly("is_unknown", &DAGNode::isUnknown)
        .def_property_readonly("is_atom", &DAGNode::isAtom)
        .def_property_readonly("is_literal", &DAGNode::isLiteral)

        // Boolean structure
        .def_property_readonly("is_true", &DAGNode::isTrue)
        .def_property_readonly("is_false", &DAGNode::isFalse)
        .def_property_readonly("is_and", &DAGNode::isAnd)
        .def_property_readonly("is_or", &DAGNode::isOr)
        .def_property_readonly("is_not", &DAGNode::isNot)
        .def_property_readonly("is_implies", &DAGNode::isImplies)
        .def_property_readonly("is_xor", &DAGNode::isXor)
        .def_property_readonly("is_ite", &DAGNode::isIte)
        .def_property_readonly("is_eq", &DAGNode::isEq)
        .def_property_readonly("is_distinct", &DAGNode::isDistinct)

        // Arithmetic
        .def_property_readonly("is_add", &DAGNode::isAdd)
        .def_property_readonly("is_sub", &DAGNode::isSub)
        .def_property_readonly("is_mul", &DAGNode::isMul)
        .def_property_readonly("is_neg", &DAGNode::isNeg)
        .def_property_readonly("is_div_int", &DAGNode::isDivInt)
        .def_property_readonly("is_div_real", &DAGNode::isDivReal)
        .def_property_readonly("is_mod", &DAGNode::isMod)
        .def_property_readonly("is_le", &DAGNode::isLe)
        .def_property_readonly("is_lt", &DAGNode::isLt)
        .def_property_readonly("is_ge", &DAGNode::isGe)
        .def_property_readonly("is_gt", &DAGNode::isGt)
        .def_property_readonly("is_arith_op", &DAGNode::isArithOp)
        .def_property_readonly("is_arith_comp", &DAGNode::isArithComp)
        .def_property_readonly("is_arith_term", &DAGNode::isArithTerm)

        // Constant categories
        .def_property_readonly("is_const_bool", &DAGNode::isCBool)
        .def_property_readonly("is_const_int", &DAGNode::isCInt)
        .def_property_readonly("is_const_real", &DAGNode::isCReal)
        .def_property_readonly("is_const_bv", &DAGNode::isCBV)
        .def_property_readonly("is_const_fp", &DAGNode::isCFP)
        .def_property_readonly("is_const_str", &DAGNode::isCStr)
        .def_property_readonly("is_numeral", &DAGNode::isNumeral)
        .def_property_readonly("is_pi", &DAGNode::isPi)
        .def_property_readonly("is_e", &DAGNode::isE)
        .def_property_readonly("is_infinity", &DAGNode::isInfinity)
        .def_property_readonly("is_nan", &DAGNode::isNaN)
        .def_property_readonly("is_epsilon", &DAGNode::isEpsilon)

        // BV / FP / String / Array / quantifier structure
        .def_property_readonly("is_bv_op", &DAGNode::isBVOp)
        .def_property_readonly("is_bv_term", &DAGNode::isBVTerm)
        .def_property_readonly("is_bv_atom", &DAGNode::isBVAtom)
        .def_property_readonly("is_fp_op", &DAGNode::isFPOp)
        .def_property_readonly("is_fp_term", &DAGNode::isFPTerm)
        .def_property_readonly("is_fp_atom", &DAGNode::isFPAtom)
        .def_property_readonly("is_str_op", &DAGNode::isStrOp)
        .def_property_readonly("is_str_atom", &DAGNode::isStrAtom)
        .def_property_readonly("is_select", &DAGNode::isSelect)
        .def_property_readonly("is_store", &DAGNode::isStore)
        .def_property_readonly("is_const_array", &DAGNode::isConstArray)
        .def_property_readonly("is_array", &DAGNode::isArray)
        .def_property_readonly("is_let", &DAGNode::isLet)
        .def_property_readonly("is_let_chain", &DAGNode::isLetChain)
        .def_property_readonly("is_quant_var", &DAGNode::isQuantVar)
        .def_property_readonly("is_temp_var", &DAGNode::isTempVar)
        .def_property_readonly("is_uf_application", &DAGNode::isUFApplication)
        .def_property_readonly("is_func_def", &DAGNode::isFuncDef)
        .def_property_readonly("is_func_dec", &DAGNode::isFuncDec)
        .def_property_readonly("is_func_application", &DAGNode::isFuncApplication)

        // Kind of the node as raw string via getKind is covered by .kind
        .def("__len__", &DAGNode::getChildrenSize)
        .def("__getitem__", [](const DAGNode& n, py::ssize_t i) {
            py::ssize_t size = static_cast<py::ssize_t>(n.getChildrenSize());
            if (i < 0) i += size;
            if (i < 0 || i >= size) throw py::index_error("Node child index out of range");
            return n.getChild(static_cast<int>(i));
        }, py::arg("index"))
        .def("__iter__", [](const DAGNode& n) {
            py::list result;
            for (const auto& child : n.getChildren()) result.append(child);
            return py::iter(result);
        })
        .def("__hash__", &DAGNode::hashCode)
        .def("__eq__", [](const NodePtr& a, const NodePtr& b) {
            if (!b) return false;
            return a->isEquivalentTo(b);
        }, py::is_operator())
        .def("__ne__", [](const NodePtr& a, const NodePtr& b) {
            if (!b) return true;
            return !a->isEquivalentTo(b);
        }, py::is_operator())
        .def("to_smt2", [](const NodePtr& n) { return dumpSMTLIB2(n); },
            "SMT-LIB2 text of this expression (parser-independent)")
        .def("__str__", [](const NodePtr& n) { return dumpSMTLIB2(n); })
        .def("__repr__", [](const NodePtr& n) {
            // A shared DAG expands to exponentially long text, so check the
            // dump size BEFORE dumping (pytest calls repr on every failure).
            std::string text;
            if (dump_size_estimate(n, 4096) >= 4096) {
                text = "<" + std::to_string(n->getChildrenSize()) + " children, large>";
            } else {
                text = dumpSMTLIB2(n);
                if (text.size() > 64) text = text.substr(0, 61) + "...";
            }
            return "<Node " + kindToString(n->getKind()) + " '" + text + "'>";
        });

    // ===== Model =====
    py::class_<Model, ModelPtr>(m, "Model", "Assignment of variables to values")
        .def(py::init<>())
        .def("__getitem__", [](Model& mo, const std::string& name) {
            auto v = mo.get(name);
            if (!v || v->isNull() || v->isUnknown()) throw py::key_error(name);
            return v;
        }, py::arg("name"))
        .def("__contains__", [](Model& mo, const std::string& name) {
            auto v = mo.get(name);
            return v && !v->isNull() && !v->isUnknown();
        }, py::arg("name"))
        .def("__len__", &Model::size)
        .def("get", [](Model& mo, const std::string& name, py::object default_val) {
            auto v = mo.get(name);
            if (!v || v->isNull() || v->isUnknown()) return default_val;
            return py::cast(v);
        }, py::arg("name"), py::arg("default") = py::none())
        .def("add", [](Model& mo, const std::string& name, const NodePtr& value) {
            mo.add(name, value);
        }, py::arg("name"), py::arg("value"), "Add / overwrite an assignment")
        .def("keys", [](const Model& mo) {
            std::vector<std::string> keys;
            for (const auto& p : mo.getPairs()) keys.push_back(p.first);
            return keys;
        })
        .def("values", &Model::getValues)
        .def("items", &Model::getPairs)
        .def_property_readonly("is_empty", &Model::isEmpty)
        .def("__str__", &Model::toString)
        .def("__repr__", [](Model& mo) {
            return "<Model with " + std::to_string(mo.size()) + " assignments>";
        });

    // ===== Objective =====
    py::class_<MetaObjective, std::shared_ptr<MetaObjective>>(m, "MetaObjective",
            "Base class for optimization objectives")
        .def_property_readonly("kind", &MetaObjective::getObjectiveKind)
        .def_property_readonly("group_id", &MetaObjective::getGroupID)
        .def_property_readonly("is_minimize", &MetaObjective::isMinimize)
        .def_property_readonly("is_maximize", &MetaObjective::isMaximize)
        .def_property_readonly("is_maxsat", &MetaObjective::isMaxSAT)
        .def_property_readonly("is_minsat", &MetaObjective::isMinSAT)
        .def_property_readonly("is_lex", &MetaObjective::isLexOptimize)
        .def_property_readonly("is_pareto", &MetaObjective::isParetoOptimize)
        .def_property_readonly("is_box", &MetaObjective::isBoxOptimize)
        .def_property_readonly("is_single", &MetaObjective::isSingleObjective)
        .def_property_readonly("is_multi", &MetaObjective::isMultiObjective)
        .def_property_readonly("term", [](const MetaObjective& o) {
            return opt_node(o.getObjectiveTerm());
        }, "Objective term (None for maxsat/minsat or multi-objectives)")
        .def_property_readonly("num_subobjectives", [](const MetaObjective& o) {
            return o.getObjectiveSize();
        })
        .def("subobjective", [](const MetaObjective& o, size_t i) {
            if (i >= o.getObjectiveSize()) {
                throw py::index_error("sub-objective index out of range");
            }
            return o.getObjective(i);
        }, py::arg("index"), "Get the i-th sub-objective (multi-objectives)")
        .def_property_readonly("subobjectives", [](const MetaObjective& o) {
            std::vector<std::shared_ptr<MetaObjective>> subs;
            for (size_t i = 0; i < o.getObjectiveSize(); ++i) subs.push_back(o.getObjective(i));
            return subs;
        })
        .def("__repr__", [](const MetaObjective& o) {
            std::string k =
                o.isMinimize() ? "minimize" :
                o.isMaximize() ? "maximize" :
                o.isMaxSAT()   ? "maxsat"   :
                o.isMinSAT()   ? "minsat"   :
                o.isLexOptimize() ? "lex-optimize" :
                o.isParetoOptimize() ? "pareto-optimize" :
                o.isBoxOptimize() ? "box-optimize" : "objective";
            return "<Objective " + k + ">";
        });

    py::class_<Objective, MetaObjective, std::shared_ptr<Objective>>(m, "Objective",
        "Optimization objective (single or multi)");

    // ===== Command / Script =====
    py::class_<Command>(m, "Command", "A parsed SMT-LIB command")
        .def_readonly("type", &Command::type)
        .def_readonly("index", &Command::index)
        .def_readonly("original", &Command::original)
        .def_readonly("line_number", &Command::line_number)
        .def_property_readonly("expr", [](const Command& c) { return opt_node(c.expr); })
        .def_readonly("name", &Command::name)
        .def_property_readonly("sort", [](const Command& c) { return opt_sort(c.sort); })
        .def_readonly("params", &Command::params)
        .def_readonly("group_id", &Command::group_id)
        .def_property_readonly("weight", [](const Command& c) { return opt_node(c.weight); })
        .def_readonly("push_pop_level", &Command::push_pop_level)
        .def_readonly("logic", &Command::logic)
        .def_readonly("value_terms", &Command::value_terms)
        .def_readonly("assumptions", &Command::assumptions)
        .def_readonly("keyword", &Command::keyword)
        .def_property_readonly("is_assert", &Command::isAssert)
        .def_property_readonly("is_push", &Command::isPush)
        .def_property_readonly("is_pop", &Command::isPop)
        .def_property_readonly("is_reset", &Command::isReset)
        .def_property_readonly("is_reset_assertions", &Command::isResetAssertions)
        .def("__repr__", [](const Command& c) {
            return "<Command type=" + std::to_string(static_cast<int>(c.type)) +
                   " line=" + std::to_string(c.line_number) + ">";
        });

    py::class_<Script>(m, "Script", "Ordered sequence of parsed commands")
        .def("__len__", &Script::size)
        .def("__getitem__", [](const Script& s, py::ssize_t i) {
            py::ssize_t size = static_cast<py::ssize_t>(s.size());
            if (i < 0) i += size;
            if (i < 0 || i >= size) throw py::index_error("Script index out of range");
            return s[static_cast<size_t>(i)];
        }, py::arg("index"))
        .def("__iter__", [](const Script& s) {
            py::list result;
            for (size_t i = 0; i < s.size(); ++i) result.append(s[i]);
            return py::iter(result);
        })
        .def_property_readonly("commands", &Script::commands)
        .def("__repr__", [](const Script& s) {
            return "<Script with " + std::to_string(s.size()) + " commands>";
        });

    // ===== Parser =====
    py::class_<Parser, std::shared_ptr<Parser>> parser(m, "Parser",
        "SMT-LIB2 / OMT parser, expression builder and formula toolbox");

    parser.def(py::init<>());

    // ---- Parsing ----
    parser
        .def("parse_file", [](Parser& p, const std::string& path) -> Parser& {
            if (!p.parse(path)) {
                throw BindParseError("failed to parse file '" + path +
                                     "' (details on stdout)");
            }
            return p;
        }, py::return_value_policy::reference_internal, py::arg("path"),
           "Parse an SMT-LIB2/OMT file. Raises ParseError on failure.")
        .def("parse_string", [](Parser& p, const std::string& text) -> Parser& {
            if (!p.parseStr(text)) {
                throw BindParseError("failed to parse SMT-LIB2 input (details on stdout)");
            }
            return p;
        }, py::return_value_policy::reference_internal, py::arg("text"),
           "Parse SMT-LIB2/OMT commands from a string. Raises ParseError on failure.")
        .def("assert_", [](Parser& p, const std::string& constraint) {
            if (!p.assert(constraint)) {
                throw BindParseError("failed to assert '" + constraint + "'");
            }
        }, py::arg("constraint"), "Assert an SMT-LIB2 term given as a string")
        .def("assert_", [](Parser& p, const NodePtr& node) {
            if (!node || node->isErr() || node->isNull()) {
                throw py::value_error("assert_: invalid node");
            }
            // The C++ layer accepts any node; enforce SMT-LIB typing here.
            if (!node->getSort() || !node->getSort()->isBool()) {
                throw py::value_error("assert_: expected a Bool-sorted term, got sort '" +
                    (node->getSort() ? node->getSort()->toString() : std::string("?")) + "'");
            }
            if (!p.assert(node)) {
                throw py::value_error("assert_: node was rejected");
            }
        }, py::arg("node"), "Assert a Bool-sorted expression node")
        .def("expr", [](Parser& p, const std::string& text) {
            return checked(p.mkExpr(text), "expr");
        }, py::arg("text"),
           "Build an expression node from an SMT-LIB2 term string")
        .def("parse_model", [](Parser& p, const std::string& text, bool only_declared) {
            auto model = p.parseModel(text, only_declared);
            if (!model) throw BindParseError("failed to parse model");
            return model;
        }, py::arg("text"), py::arg("only_declared") = false,
           "Parse solver model output (e.g. cvc5/z3 get-model text) into a Model");

    // ---- Results / contents ----
    parser
        .def_property_readonly("assertions", &Parser::getAssertions)
        .def_property_readonly("assumptions", &Parser::getAssumptions)
        .def_property_readonly("soft_assertions", &Parser::getSoftAssertions)
        .def_property_readonly("soft_weights", &Parser::getSoftWeights)
        .def_property_readonly("grouped_assertions", &Parser::getGroupedAssertions)
        .def_property_readonly("grouped_soft_assertions", &Parser::getGroupedSoftAssertions)
        .def_property_readonly("objectives", &Parser::getObjectives)
        .def_property_readonly("variables", &Parser::getVariables)
        .def_property_readonly("declared_variables", &Parser::getDeclaredVariables)
        .def_property_readonly("functions", &Parser::getFunctions)
        .def_property_readonly("uninterpreted_sorts", [](const Parser& p) {
            std::vector<std::string> names;
            std::unordered_set<std::string> seen;
            const auto symbols = p.getSymbolManager();
            const auto& sorts = symbols->getSortKeyMap();
            for (const auto& name : symbols->getSortOrder()) {
                const auto it = sorts.find(name);
                // A zero-parameter define-sort alias can point at the same
                // SK_DEC object as its target. Count the canonical constructor
                // key only, and deduplicate live names after temporary scope
                // registrations that leave historical order entries behind.
                if (it != sorts.end() && it->second && it->second->isDec()
                    && it->second->name == name && seen.insert(name).second) {
                    names.push_back(name);
                }
            }
            return names;
        }, "Declared uninterpreted sort names, including parameterized sort constructors")
        .def_property_readonly("logic", [](const Parser& p) {
            return p.getOptions()->getLogic();
        })
        .def_property_readonly("script", &Parser::getScript,
            py::return_value_policy::reference_internal,
            "Recorded command Script (enable with set_command_logging(True))")
        .def_property_readonly("result_type", [](Parser& p) { return p.getResultType(); },
            "Result recorded while parsing (sat/unsat response in the input)")
        .def("check_sat", &Parser::checkSat,
            "Trivial satisfiability check: SAT/UNSAT when every assertion "
            "folds to a constant, UNKNOWN otherwise")
        .def_property_readonly("node_count", [](Parser& p) { return p.getNodeCount(); })
        .def("get_model", [](Parser& p) -> py::object {
            auto model = p.getModel();
            if (!model) return py::none();
            return py::cast(model);
        }, "Model recorded while parsing (None if absent)")
        .def("get_variable", [](Parser& p, const std::string& name) {
            if (!p.isDeclaredVariable(name)) throw py::key_error(name);
            return p.getVariable(name);
        }, py::arg("name"))
        .def("is_declared_variable", &Parser::isDeclaredVariable, py::arg("name"))
        .def("is_declared_function", &Parser::isDeclaredFunction, py::arg("name"));

    // ---- Options ----
    parser
        .def("set_option", py::overload_cast<const std::string&, const std::string&>(
            &Parser::setOption), py::arg("key"), py::arg("value"))
        .def("set_option", py::overload_cast<const std::string&, const bool&>(
            &Parser::setOption), py::arg("key"), py::arg("value"))
        .def("set_option", py::overload_cast<const std::string&, const int&>(
            &Parser::setOption), py::arg("key"), py::arg("value"))
        .def("set_option", py::overload_cast<const std::string&, const double&>(
            &Parser::setOption), py::arg("key"), py::arg("value"))
        .def("options_smt2", &Parser::optionToString,
            "All recorded options as SMT-LIB2 text")
        .def("set_strict_smtlib", &Parser::setStrictSmtlib, py::arg("strict"),
            "Enforce strict SMT-LIB FloatingPoint surface syntax")
        .def("get_strict_smtlib", &Parser::getStrictSmtlib)
        .def("set_evaluate_precision", [](Parser& p, long precision) {
            p.setEvaluatePrecision(static_cast<mpfr_prec_t>(precision));
        }, py::arg("precision"), "MPFR precision (bits) used by evaluate()")
        .def("set_evaluate_use_floating", &Parser::setEvaluateUseFloating,
            py::arg("use_floating"))
        .def("get_evaluate_use_floating", &Parser::getEvaluateUseFloating)
        .def("set_command_logging", &Parser::setCommandLogging, py::arg("enable"),
            "Record every parsed command into parser.script");

    // ---- Incremental interface ----
    parser
        .def("push", [](Parser& p, size_t n) {
            if (!p.push(n)) throw py::value_error("push failed");
        }, py::arg("n") = 1)
        .def("pop", [](Parser& p, size_t n) {
            if (!p.pop(n)) throw py::value_error("pop failed (no matching push?)");
        }, py::arg("n") = 1)
        .def("reset", [](Parser& p) { p.reset(); })
        .def("reset_assertions", [](Parser& p) { p.resetAssertions(); });

    // ---- Sorts ----
    parser
        .def("int_sort", &Parser::mkIntSort)
        .def("real_sort", &Parser::mkRealSort)
        .def("bool_sort", &Parser::mkBoolSort)
        .def("string_sort", &Parser::mkStrSort)
        .def("regex_sort", &Parser::mkRegSort)
        .def("rounding_mode_sort", &Parser::mkRoundingModeSort)
        .def("bv_sort", [](Parser& p, size_t width) {
            check_bv_width_positive(width, "bv_sort");
            return p.mkBVSort(width);
        }, py::arg("width"))
        .def("fp_sort", &Parser::mkFPSort, py::arg("exponent"), py::arg("significand"))
        .def("array_sort", &Parser::mkArraySort, py::arg("index"), py::arg("elem"))
        .def("declare_sort", &Parser::mkSortDec, py::arg("name"), py::arg("arity"))
        .def("define_sort", &Parser::mkSortDef, py::arg("name"), py::arg("params"),
            py::arg("out_sort"));

    // ---- Variable declarations ----
    parser
        .def("declare_var", [](Parser& p, const std::string& name, const std::string& sort) {
            return checked(p.declareVar(name, sort), "declare_var");
        }, py::arg("name"), py::arg("sort"),
           "Declare a variable with a sort given as SMT-LIB2 text (e.g. 'Int', '(_ BitVec 8)')")
        .def("declare_var", [](Parser& p, const std::string& name, const SortPtr& sort) {
            return checked(p.declareVar(name, sort), "declare_var");
        }, py::arg("name"), py::arg("sort"))
        .def("var_bool", [](Parser& p, const std::string& name) {
            return checked(p.mkVarBool(name), "var_bool");
        }, py::arg("name"))
        .def("var_int", [](Parser& p, const std::string& name) {
            return checked(p.mkVarInt(name), "var_int");
        }, py::arg("name"))
        .def("var_real", [](Parser& p, const std::string& name) {
            return checked(p.mkVarReal(name), "var_real");
        }, py::arg("name"))
        .def("var_bv", [](Parser& p, const std::string& name, size_t width) {
            check_bv_width_positive(width, "var_bv");
            return checked(p.mkVarBv(name, width), "var_bv");
        }, py::arg("name"), py::arg("width"))
        .def("var_fp", [](Parser& p, const std::string& name, size_t e, size_t s) {
            return checked(p.mkVarFp(name, e, s), "var_fp");
        }, py::arg("name"), py::arg("exponent"), py::arg("significand"))
        .def("var_str", [](Parser& p, const std::string& name) {
            return checked(p.mkVarStr(name), "var_str");
        }, py::arg("name"))
        .def("var_array", [](Parser& p, const std::string& name, const SortPtr& index,
                             const SortPtr& elem) {
            return checked(p.mkArray(name, index, elem), "var_array");
        }, py::arg("name"), py::arg("index"), py::arg("elem"))
        .def("var_rounding_mode", [](Parser& p, const std::string& name) {
            return checked(p.mkVarRoundingMode(name), "var_rounding_mode");
        }, py::arg("name"))
        .def("quant_var", [](Parser& p, const std::string& name, const SortPtr& sort) {
            return checked(p.mkQuantVar(name, sort), "quant_var");
        }, py::arg("name"), py::arg("sort"));

    // ---- Constants ----
    parser
        .def("true_", &Parser::mkTrue)
        .def("false_", &Parser::mkFalse)
        .def("const_int", [](Parser& p, const py::object& v) {
            return checked(p.mkConstInt(int_like_to_string(v, "const_int")), "const_int");
        }, py::arg("value"), "Integer constant from a Python int (arbitrary precision) or str")
        .def("const_real", [](Parser& p, const py::object& v) {
            if (py::isinstance<py::float_>(v)) {
                return checked(p.mkConstReal(v.cast<double>()), "const_real");
            }
            return checked(p.mkConstReal(int_like_to_string(v, "const_real")), "const_real");
        }, py::arg("value"), "Real constant from float, int or str (e.g. '1/3')")
        .def("const_str", [](Parser& p, const std::string& v) {
            return checked(p.mkConstStr(v), "const_str");
        }, py::arg("value"), "String constant; pass raw text WITH surrounding quotes "
           "or an SMT-LIB literal (e.g. '\"abc\"')")
        .def("const_bv", [](Parser& p, const py::object& v, size_t width) {
            check_bv_width_positive(width, "const_bv");
            return checked(p.mkConstBv(int_like_to_string(v, "const_bv"), width), "const_bv");
        }, py::arg("value"), py::arg("width"),
           "BitVec constant from int/str decimal value and bit width")
        .def("const_fp", [](Parser& p, const std::string& v, size_t e, size_t s) {
            return checked(p.mkConstFp(v, e, s), "const_fp");
        }, py::arg("value"), py::arg("exponent"), py::arg("significand"))
        .def("rounding_mode", [](Parser& p, const std::string& mode) {
            return checked(p.mkRoundingMode(mode), "rounding_mode");
        }, py::arg("mode"), "Rounding-mode constant: RNE, RNA, RTP, RTN, RTZ")
        .def("pi", &Parser::mkPi)
        .def("e", &Parser::mkE)
        .def("epsilon", &Parser::mkEpsilon)
        .def("nan", [](Parser& p) { return p.mkNaN(nullptr); })
        .def("infinity", [](Parser& p, const SortPtr& sort) {
            return checked(p.mkInfinity(sort), "infinity");
        }, py::arg("sort"))
        .def("pos_infinity", [](Parser& p) { return p.mkPosInfinity(nullptr); })
        .def("neg_infinity", [](Parser& p) { return p.mkNegInfinity(nullptr); })
        .def("const_array", [](Parser& p, const SortPtr& sort, const NodePtr& value) {
            return checked(p.mkConstArray(sort, value), "const_array");
        }, py::arg("sort"), py::arg("value"),
           "Constant array of the given array sort with default element value");

    // ---- Boolean operators ----
    parser
        .def("not_", [](Parser& p, const NodePtr& a) {
            return checked(p.mkNot(a), "not_");
        }, py::arg("a"))
        .def("and_", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkAnd(a, b), "and_");
        }, py::arg("a"), py::arg("b"))
        .def("and_", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkAnd(args), "and_");
        }, py::arg("args"))
        .def("or_", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkOr(a, b), "or_");
        }, py::arg("a"), py::arg("b"))
        .def("or_", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkOr(args), "or_");
        }, py::arg("args"))
        .def("implies", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkImplies(a, b), "implies");
        }, py::arg("a"), py::arg("b"))
        .def("xor_", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkXor(a, b), "xor_");
        }, py::arg("a"), py::arg("b"))
        .def("xor_", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkXor(args), "xor_");
        }, py::arg("args"))
        .def("ite", [](Parser& p, const NodePtr& c, const NodePtr& t, const NodePtr& e) {
            return checked(p.mkIte(c, t, e), "ite");
        }, py::arg("cond"), py::arg("then_"), py::arg("else_"))
        .def("eq", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkEq(a, b), "eq");
        }, py::arg("a"), py::arg("b"))
        .def("eq", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkEq(args), "eq");
        }, py::arg("args"))
        .def("distinct", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkDistinct(a, b), "distinct");
        }, py::arg("a"), py::arg("b"))
        .def("distinct", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkDistinct(args), "distinct");
        }, py::arg("args"));

    // ---- Arithmetic ----
    parser
        .def("add", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkAdd(a, b), "add");
        }, py::arg("a"), py::arg("b"))
        .def("add", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkAdd(args), "add");
        }, py::arg("args"))
        .def("sub", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkSub(a, b), "sub");
        }, py::arg("a"), py::arg("b"))
        .def("sub", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkSub(args), "sub");
        }, py::arg("args"))
        .def("mul", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkMul(a, b), "mul");
        }, py::arg("a"), py::arg("b"))
        .def("mul", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkMul(args), "mul");
        }, py::arg("args"))
        .def("neg", [](Parser& p, const NodePtr& a) {
            return checked(p.mkNeg(a), "neg");
        }, py::arg("a"))
        .def("div", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkDiv(a, b), "div");
        }, py::arg("a"), py::arg("b"), "Division (dispatches to Int or Real by sort)")
        .def("div_int", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkDivInt(a, b), "div_int");
        }, py::arg("a"), py::arg("b"))
        .def("div_real", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkDivReal(a, b), "div_real");
        }, py::arg("a"), py::arg("b"))
        .def("mod", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkMod(a, b), "mod");
        }, py::arg("a"), py::arg("b"))
        .def("abs_", [](Parser& p, const NodePtr& a) {
            return checked(p.mkAbs(a), "abs_");
        }, py::arg("a"))
        .def("pow", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkPow(a, b), "pow");
        }, py::arg("a"), py::arg("b"))
        .def("pow2", [](Parser& p, const NodePtr& a) {
            return checked(p.mkPow2(a), "pow2");
        }, py::arg("a"))
        .def("sqrt", [](Parser& p, const NodePtr& a) {
            return checked(p.mkSqrt(a), "sqrt");
        }, py::arg("a"))
        .def("safe_sqrt", [](Parser& p, const NodePtr& a) {
            return checked(p.mkSafeSqrt(a), "safe_sqrt");
        }, py::arg("a"))
        .def("ceil", [](Parser& p, const NodePtr& a) {
            return checked(p.mkCeil(a), "ceil");
        }, py::arg("a"))
        .def("floor", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFloor(a), "floor");
        }, py::arg("a"))
        .def("round", [](Parser& p, const NodePtr& a) {
            return checked(p.mkRound(a), "round");
        }, py::arg("a"))
        .def("exp", [](Parser& p, const NodePtr& a) {
            return checked(p.mkExp(a), "exp");
        }, py::arg("a"))
        .def("ln", [](Parser& p, const NodePtr& a) {
            return checked(p.mkLn(a), "ln");
        }, py::arg("a"))
        .def("lg", [](Parser& p, const NodePtr& a) {
            return checked(p.mkLg(a), "lg");
        }, py::arg("a"))
        .def("lb", [](Parser& p, const NodePtr& a) {
            return checked(p.mkLb(a), "lb");
        }, py::arg("a"))
        .def("log", [](Parser& p, const NodePtr& base, const NodePtr& a) {
            return checked(p.mkLog(base, a), "log");
        }, py::arg("base"), py::arg("a"))
        .def("sin", [](Parser& p, const NodePtr& a) { return checked(p.mkSin(a), "sin"); })
        .def("cos", [](Parser& p, const NodePtr& a) { return checked(p.mkCos(a), "cos"); })
        .def("tan", [](Parser& p, const NodePtr& a) { return checked(p.mkTan(a), "tan"); })
        .def("cot", [](Parser& p, const NodePtr& a) { return checked(p.mkCot(a), "cot"); })
        .def("sec", [](Parser& p, const NodePtr& a) { return checked(p.mkSec(a), "sec"); })
        .def("csc", [](Parser& p, const NodePtr& a) { return checked(p.mkCsc(a), "csc"); })
        .def("asin", [](Parser& p, const NodePtr& a) { return checked(p.mkAsin(a), "asin"); })
        .def("acos", [](Parser& p, const NodePtr& a) { return checked(p.mkAcos(a), "acos"); })
        .def("atan", [](Parser& p, const NodePtr& a) { return checked(p.mkAtan(a), "atan"); })
        .def("atan2", [](Parser& p, const NodePtr& y, const NodePtr& x) {
            return checked(p.mkAtan2(y, x), "atan2");
        }, py::arg("y"), py::arg("x"))
        .def("sinh", [](Parser& p, const NodePtr& a) { return checked(p.mkSinh(a), "sinh"); })
        .def("cosh", [](Parser& p, const NodePtr& a) { return checked(p.mkCosh(a), "cosh"); })
        .def("tanh", [](Parser& p, const NodePtr& a) { return checked(p.mkTanh(a), "tanh"); })
        .def("asinh", [](Parser& p, const NodePtr& a) { return checked(p.mkAsinh(a), "asinh"); })
        .def("acosh", [](Parser& p, const NodePtr& a) { return checked(p.mkAcosh(a), "acosh"); })
        .def("atanh", [](Parser& p, const NodePtr& a) { return checked(p.mkAtanh(a), "atanh"); })
        .def("gcd", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkGcd(a, b), "gcd");
        }, py::arg("a"), py::arg("b"))
        .def("lcm", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkLcm(a, b), "lcm");
        }, py::arg("a"), py::arg("b"))
        .def("factorial", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFact(a), "factorial");
        }, py::arg("a"))
        .def("max_", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkMax(args), "max_");
        }, py::arg("args"))
        .def("min_", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkMin(args), "min_");
        }, py::arg("args"))
        .def("le", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkLe(a, b), "le");
        }, py::arg("a"), py::arg("b"))
        .def("le", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkLe(args), "le");
        }, py::arg("args"))
        .def("lt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkLt(a, b), "lt");
        }, py::arg("a"), py::arg("b"))
        .def("lt", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkLt(args), "lt");
        }, py::arg("args"))
        .def("ge", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkGe(a, b), "ge");
        }, py::arg("a"), py::arg("b"))
        .def("ge", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkGe(args), "ge");
        }, py::arg("args"))
        .def("gt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkGt(a, b), "gt");
        }, py::arg("a"), py::arg("b"))
        .def("gt", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkGt(args), "gt");
        }, py::arg("args"))
        .def("to_int", [](Parser& p, const NodePtr& a) {
            return checked(p.mkToInt(a), "to_int");
        }, py::arg("a"))
        .def("to_real", [](Parser& p, const NodePtr& a) {
            return checked(p.mkToReal(a), "to_real");
        }, py::arg("a"))
        .def("is_int_pred", [](Parser& p, const NodePtr& a) {
            return checked(p.mkIsInt(a), "is_int_pred");
        }, py::arg("a"), "(is_int a) predicate node")
        .def("is_divisible", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkIsDivisible(a, b), "is_divisible");
        }, py::arg("a"), py::arg("b"))
        .def("is_prime", [](Parser& p, const NodePtr& a) {
            return checked(p.mkIsPrime(a), "is_prime");
        }, py::arg("a"))
        .def("is_even", [](Parser& p, const NodePtr& a) {
            return checked(p.mkIsEven(a), "is_even");
        }, py::arg("a"))
        .def("is_odd", [](Parser& p, const NodePtr& a) {
            return checked(p.mkIsOdd(a), "is_odd");
        }, py::arg("a"));

    // ---- BitVectors ----
    // Helper to wrap an integer amount as a const-int node.
    auto amount_node = [](Parser& p, size_t v) {
        return p.mkConstInt(std::to_string(v));
    };
    parser
        .def("bv_not", [](Parser& p, const NodePtr& a) {
            return checked(p.mkBvNot(a), "bv_not");
        }, py::arg("a"))
        .def("bv_and", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_and");
            return checked(p.mkBvAnd(a, b), "bv_and");
        }, py::arg("a"), py::arg("b"))
        .def("bv_or", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_or");
            return checked(p.mkBvOr(a, b), "bv_or");
        }, py::arg("a"), py::arg("b"))
        .def("bv_xor", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_xor");
            return checked(p.mkBvXor(a, b), "bv_xor");
        }, py::arg("a"), py::arg("b"))
        .def("bv_nand", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_nand");
            return checked(p.mkBvNand(a, b), "bv_nand");
        }, py::arg("a"), py::arg("b"))
        .def("bv_nor", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_nor");
            return checked(p.mkBvNor(a, b), "bv_nor");
        }, py::arg("a"), py::arg("b"))
        .def("bv_xnor", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_xnor");
            return checked(p.mkBvXnor(a, b), "bv_xnor");
        }, py::arg("a"), py::arg("b"))
        .def("bv_comp", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_comp");
            return checked(p.mkBvComp(a, b), "bv_comp");
        }, py::arg("a"), py::arg("b"))
        .def("bv_neg", [](Parser& p, const NodePtr& a) {
            return checked(p.mkBvNeg(a), "bv_neg");
        }, py::arg("a"))
        .def("bv_add", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_add");
            return checked(p.mkBvAdd(a, b), "bv_add");
        }, py::arg("a"), py::arg("b"))
        .def("bv_sub", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_sub");
            return checked(p.mkBvSub(a, b), "bv_sub");
        }, py::arg("a"), py::arg("b"))
        .def("bv_mul", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_mul");
            return checked(p.mkBvMul(a, b), "bv_mul");
        }, py::arg("a"), py::arg("b"))
        .def("bv_udiv", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_udiv");
            return checked(p.mkBvUdiv(a, b), "bv_udiv");
        }, py::arg("a"), py::arg("b"))
        .def("bv_urem", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_urem");
            return checked(p.mkBvUrem(a, b), "bv_urem");
        }, py::arg("a"), py::arg("b"))
        .def("bv_sdiv", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_sdiv");
            return checked(p.mkBvSdiv(a, b), "bv_sdiv");
        }, py::arg("a"), py::arg("b"))
        .def("bv_srem", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_srem");
            return checked(p.mkBvSrem(a, b), "bv_srem");
        }, py::arg("a"), py::arg("b"))
        .def("bv_smod", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_smod");
            return checked(p.mkBvSmod(a, b), "bv_smod");
        }, py::arg("a"), py::arg("b"))
        .def("bv_shl", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_shl");
            return checked(p.mkBvShl(a, b), "bv_shl");
        }, py::arg("a"), py::arg("b"))
        .def("bv_lshr", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_lshr");
            return checked(p.mkBvLshr(a, b), "bv_lshr");
        }, py::arg("a"), py::arg("b"))
        .def("bv_ashr", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_ashr");
            return checked(p.mkBvAshr(a, b), "bv_ashr");
        }, py::arg("a"), py::arg("b"))
        .def("bv_concat", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkBvConcat(args), "bv_concat");
        }, py::arg("args"))
        .def("bv_extract", [amount_node](Parser& p, const NodePtr& a, size_t high, size_t low) {
            return checked(p.mkBvExtract(a, amount_node(p, high), amount_node(p, low)),
                           "bv_extract");
        }, py::arg("a"), py::arg("high"), py::arg("low"))
        .def("bv_repeat", [amount_node](Parser& p, const NodePtr& a, size_t count) {
            return checked(p.mkBvRepeat(a, amount_node(p, count)), "bv_repeat");
        }, py::arg("a"), py::arg("count"))
        .def("bv_zero_extend", [amount_node](Parser& p, const NodePtr& a, size_t count) {
            return checked(p.mkBvZeroExt(a, amount_node(p, count)), "bv_zero_extend");
        }, py::arg("a"), py::arg("count"))
        .def("bv_sign_extend", [amount_node](Parser& p, const NodePtr& a, size_t count) {
            return checked(p.mkBvSignExt(a, amount_node(p, count)), "bv_sign_extend");
        }, py::arg("a"), py::arg("count"))
        .def("bv_rotate_left", [amount_node](Parser& p, const NodePtr& a, size_t count) {
            return checked(p.mkBvRotateLeft(a, amount_node(p, count)), "bv_rotate_left");
        }, py::arg("a"), py::arg("count"))
        .def("bv_rotate_right", [amount_node](Parser& p, const NodePtr& a, size_t count) {
            return checked(p.mkBvRotateRight(a, amount_node(p, count)), "bv_rotate_right");
        }, py::arg("a"), py::arg("count"))
        .def("bv_ult", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_ult");
            return checked(p.mkBvUlt(a, b), "bv_ult");
        }, py::arg("a"), py::arg("b"))
        .def("bv_ule", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_ule");
            return checked(p.mkBvUle(a, b), "bv_ule");
        }, py::arg("a"), py::arg("b"))
        .def("bv_ugt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_ugt");
            return checked(p.mkBvUgt(a, b), "bv_ugt");
        }, py::arg("a"), py::arg("b"))
        .def("bv_uge", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_uge");
            return checked(p.mkBvUge(a, b), "bv_uge");
        }, py::arg("a"), py::arg("b"))
        .def("bv_slt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_slt");
            return checked(p.mkBvSlt(a, b), "bv_slt");
        }, py::arg("a"), py::arg("b"))
        .def("bv_sle", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_sle");
            return checked(p.mkBvSle(a, b), "bv_sle");
        }, py::arg("a"), py::arg("b"))
        .def("bv_sgt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_sgt");
            return checked(p.mkBvSgt(a, b), "bv_sgt");
        }, py::arg("a"), py::arg("b"))
        .def("bv_sge", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            check_bv_same_width(a, b, "bv_sge");
            return checked(p.mkBvSge(a, b), "bv_sge");
        }, py::arg("a"), py::arg("b"))
        .def("bv_to_nat", [](Parser& p, const NodePtr& a) {
            return checked(p.mkBvToNat(a), "bv_to_nat");
        }, py::arg("a"))
        .def("bv_to_int", [](Parser& p, const NodePtr& a) {
            return checked(p.mkBvToInt(a), "bv_to_int");
        }, py::arg("a"))
        .def("int_to_bv", [amount_node](Parser& p, const NodePtr& a, size_t width) {
            check_bv_width_positive(width, "int_to_bv");
            return checked(p.mkIntToBv(a, amount_node(p, width)), "int_to_bv");
        }, py::arg("a"), py::arg("width"))
        .def("nat_to_bv", [amount_node](Parser& p, const NodePtr& a, size_t width) {
            return checked(p.mkNatToBv(a, amount_node(p, width)), "nat_to_bv");
        }, py::arg("a"), py::arg("width"));

    // ---- Floating point ----
    parser
        .def("fp_add", [](Parser& p, const NodePtr& rm, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpAdd({rm, a, b}), "fp_add");
        }, py::arg("rm"), py::arg("a"), py::arg("b"))
        .def("fp_sub", [](Parser& p, const NodePtr& rm, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpSub({rm, a, b}), "fp_sub");
        }, py::arg("rm"), py::arg("a"), py::arg("b"))
        .def("fp_mul", [](Parser& p, const NodePtr& rm, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpMul({rm, a, b}), "fp_mul");
        }, py::arg("rm"), py::arg("a"), py::arg("b"))
        .def("fp_div", [](Parser& p, const NodePtr& rm, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpDiv({rm, a, b}), "fp_div");
        }, py::arg("rm"), py::arg("a"), py::arg("b"))
        .def("fp_fma", [](Parser& p, const NodePtr& rm, const NodePtr& a, const NodePtr& b,
                          const NodePtr& c) {
            return checked(p.mkFpFma({rm, a, b, c}), "fp_fma");
        }, py::arg("rm"), py::arg("a"), py::arg("b"), py::arg("c"))
        .def("fp_abs", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpAbs(a), "fp_abs");
        }, py::arg("a"))
        .def("fp_neg", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpNeg(a), "fp_neg");
        }, py::arg("a"))
        .def("fp_rem", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpRem(a, b), "fp_rem");
        }, py::arg("a"), py::arg("b"))
        .def("fp_sqrt", [](Parser& p, const NodePtr& rm, const NodePtr& a) {
            return checked(p.mkFpSqrt(rm, a), "fp_sqrt");
        }, py::arg("rm"), py::arg("a"))
        .def("fp_round_to_integral", [](Parser& p, const NodePtr& rm, const NodePtr& a) {
            return checked(p.mkFpRoundToIntegral(rm, a), "fp_round_to_integral");
        }, py::arg("rm"), py::arg("a"))
        .def("fp_min", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpMin({a, b}), "fp_min");
        }, py::arg("a"), py::arg("b"))
        .def("fp_max", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpMax({a, b}), "fp_max");
        }, py::arg("a"), py::arg("b"))
        .def("fp_le", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpLe(a, b), "fp_le");
        }, py::arg("a"), py::arg("b"))
        .def("fp_lt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpLt(a, b), "fp_lt");
        }, py::arg("a"), py::arg("b"))
        .def("fp_ge", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpGe(a, b), "fp_ge");
        }, py::arg("a"), py::arg("b"))
        .def("fp_gt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpGt(a, b), "fp_gt");
        }, py::arg("a"), py::arg("b"))
        .def("fp_eq", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkFpEq(a, b), "fp_eq");
        }, py::arg("a"), py::arg("b"))
        .def("fp_is_normal", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsNormal(a), "fp_is_normal");
        }, py::arg("a"))
        .def("fp_is_subnormal", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsSubnormal(a), "fp_is_subnormal");
        }, py::arg("a"))
        .def("fp_is_zero", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsZero(a), "fp_is_zero");
        }, py::arg("a"))
        .def("fp_is_inf", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsInf(a), "fp_is_inf");
        }, py::arg("a"))
        .def("fp_is_nan", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsNaN(a), "fp_is_nan");
        }, py::arg("a"))
        .def("fp_is_neg", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsNeg(a), "fp_is_neg");
        }, py::arg("a"))
        .def("fp_is_pos", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpIsPos(a), "fp_is_pos");
        }, py::arg("a"))
        .def("fp_to_real", [](Parser& p, const NodePtr& a) {
            return checked(p.mkFpToReal(a), "fp_to_real");
        }, py::arg("a"))
        .def("fp_to_ubv", [amount_node](Parser& p, const NodePtr& rm, const NodePtr& a,
                                        size_t width) {
            return checked(p.mkFpToUbv(rm, a, amount_node(p, width)), "fp_to_ubv");
        }, py::arg("rm"), py::arg("a"), py::arg("width"))
        .def("fp_to_sbv", [amount_node](Parser& p, const NodePtr& rm, const NodePtr& a,
                                        size_t width) {
            return checked(p.mkFpToSbv(rm, a, amount_node(p, width)), "fp_to_sbv");
        }, py::arg("rm"), py::arg("a"), py::arg("width"))
        .def("to_fp", [amount_node](Parser& p, size_t e, size_t s, const NodePtr& rm,
                                    const NodePtr& a) {
            return checked(p.mkToFp(amount_node(p, e), amount_node(p, s), rm, a), "to_fp");
        }, py::arg("exponent"), py::arg("significand"), py::arg("rm"), py::arg("a"))
        .def("fp_const_from_bv", [](Parser& p, const NodePtr& sign, const NodePtr& exp,
                                    const NodePtr& mant) {
            return checked(p.mkFpConst(sign, exp, mant), "fp_const_from_bv");
        }, py::arg("sign"), py::arg("exponent"), py::arg("mantissa"),
           "(fp sign exp mant) from three BV constants");

    // ---- Arrays ----
    parser
        .def("select", [](Parser& p, const NodePtr& a, const NodePtr& i) {
            return checked(p.mkSelect(a, i), "select");
        }, py::arg("array"), py::arg("index"))
        .def("store", [](Parser& p, const NodePtr& a, const NodePtr& i, const NodePtr& v) {
            return checked(p.mkStore(a, i, v), "store");
        }, py::arg("array"), py::arg("index"), py::arg("value"));

    // ---- Strings ----
    parser
        .def("str_len", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrLen(a), "str_len");
        }, py::arg("a"))
        .def("str_concat", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkStrConcat(args), "str_concat");
        }, py::arg("args"))
        .def("str_substr", [](Parser& p, const NodePtr& s, const NodePtr& off, const NodePtr& len) {
            return checked(p.mkStrSubstr(s, off, len), "str_substr");
        }, py::arg("s"), py::arg("offset"), py::arg("length"))
        .def("str_prefixof", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrPrefixof(a, b), "str_prefixof");
        }, py::arg("a"), py::arg("b"))
        .def("str_suffixof", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrSuffixof(a, b), "str_suffixof");
        }, py::arg("a"), py::arg("b"))
        .def("str_indexof", [](Parser& p, const NodePtr& s, const NodePtr& sub, const NodePtr& off) {
            return checked(p.mkStrIndexof(s, sub, off), "str_indexof");
        }, py::arg("s"), py::arg("sub"), py::arg("offset"))
        .def("str_at", [](Parser& p, const NodePtr& s, const NodePtr& i) {
            return checked(p.mkStrCharat(s, i), "str_at");
        }, py::arg("s"), py::arg("index"))
        .def("str_update", [](Parser& p, const NodePtr& s, const NodePtr& i, const NodePtr& v) {
            return checked(p.mkStrUpdate(s, i, v), "str_update");
        }, py::arg("s"), py::arg("index"), py::arg("value"))
        .def("str_replace", [](Parser& p, const NodePtr& s, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrReplace(s, a, b), "str_replace");
        }, py::arg("s"), py::arg("old"), py::arg("new"))
        .def("str_replace_all", [](Parser& p, const NodePtr& s, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrReplaceAll(s, a, b), "str_replace_all");
        }, py::arg("s"), py::arg("old"), py::arg("new"))
        .def("str_to_lower", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrToLower(a), "str_to_lower");
        }, py::arg("a"))
        .def("str_to_upper", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrToUpper(a), "str_to_upper");
        }, py::arg("a"))
        .def("str_rev", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrRev(a), "str_rev");
        }, py::arg("a"))
        .def("str_lt", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrLt(a, b), "str_lt");
        }, py::arg("a"), py::arg("b"))
        .def("str_le", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrLe(a, b), "str_le");
        }, py::arg("a"), py::arg("b"))
        .def("str_contains", [](Parser& p, const NodePtr& a, const NodePtr& b) {
            return checked(p.mkStrContains(a, b), "str_contains");
        }, py::arg("a"), py::arg("b"))
        .def("str_is_digit", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrIsDigit(a), "str_is_digit");
        }, py::arg("a"))
        .def("str_from_int", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrFromInt(a), "str_from_int");
        }, py::arg("a"))
        .def("str_to_int", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrToInt(a), "str_to_int");
        }, py::arg("a"))
        .def("str_to_code", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrToCode(a), "str_to_code");
        }, py::arg("a"))
        .def("str_from_code", [](Parser& p, const NodePtr& a) {
            return checked(p.mkStrFromCode(a), "str_from_code");
        }, py::arg("a"))
        .def("str_in_re", [](Parser& p, const NodePtr& s, const NodePtr& r) {
            return checked(p.mkStrInReg(s, r), "str_in_re");
        }, py::arg("s"), py::arg("r"))
        .def("str_to_re", [](Parser& p, const NodePtr& s) {
            return checked(p.mkStrToReg(s), "str_to_re");
        }, py::arg("s"));

    // ---- Regular expressions ----
    parser
        .def("re_none", [](Parser& p) { return checked(p.mkRegNone(), "re_none"); })
        .def("re_all", [](Parser& p) { return checked(p.mkRegAll(), "re_all"); })
        .def("re_allchar", [](Parser& p) { return checked(p.mkRegAllChar(), "re_allchar"); })
        .def("re_concat", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkRegConcat(args), "re_concat");
        }, py::arg("args"))
        .def("re_union", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkRegUnion(args), "re_union");
        }, py::arg("args"))
        .def("re_inter", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkRegInter(args), "re_inter");
        }, py::arg("args"))
        .def("re_diff", [](Parser& p, const std::vector<NodePtr>& args) {
            return checked(p.mkRegDiff(args), "re_diff");
        }, py::arg("args"))
        .def("re_star", [](Parser& p, const NodePtr& r) {
            return checked(p.mkRegStar(r), "re_star");
        }, py::arg("r"))
        .def("re_plus", [](Parser& p, const NodePtr& r) {
            return checked(p.mkRegPlus(r), "re_plus");
        }, py::arg("r"))
        .def("re_opt", [](Parser& p, const NodePtr& r) {
            return checked(p.mkRegOpt(r), "re_opt");
        }, py::arg("r"))
        .def("re_range", [](Parser& p, const NodePtr& lo, const NodePtr& hi) {
            return checked(p.mkRegRange(lo, hi), "re_range");
        }, py::arg("lo"), py::arg("hi"))
        .def("re_complement", [](Parser& p, const NodePtr& r) {
            return checked(p.mkRegComplement(r), "re_complement");
        }, py::arg("r"));

    // ---- Quantifiers ----
    parser
        .def("forall", [](Parser& p, const std::vector<NodePtr>& vars, const NodePtr& body) {
            // The C++ convention is params = [body, var1, var2, ...]
            std::vector<NodePtr> params;
            params.reserve(vars.size() + 1);
            params.push_back(body);
            params.insert(params.end(), vars.begin(), vars.end());
            return checked(p.mkForall(params), "forall");
        }, py::arg("vars"), py::arg("body"),
           "Universal quantifier; vars are quant_var() nodes")
        .def("exists", [](Parser& p, const std::vector<NodePtr>& vars, const NodePtr& body) {
            std::vector<NodePtr> params;
            params.reserve(vars.size() + 1);
            params.push_back(body);
            params.insert(params.end(), vars.begin(), vars.end());
            return checked(p.mkExists(params), "exists");
        }, py::arg("vars"), py::arg("body"));

    // ---- Functions ----
    parser
        .def("declare_fun", [](Parser& p, const std::string& name,
                               const std::vector<SortPtr>& params, const SortPtr& out) {
            return checked(p.mkFuncDec(name, params, out), "declare_fun");
        }, py::arg("name"), py::arg("param_sorts"), py::arg("out_sort"))
        .def("define_fun", [](Parser& p, const std::string& name,
                              const std::vector<NodePtr>& params, const SortPtr& out,
                              const NodePtr& body) {
            return checked(p.mkFuncDef(name, params, out, body), "define_fun");
        }, py::arg("name"), py::arg("params"), py::arg("out_sort"), py::arg("body"))
        .def("apply_fun", [](Parser& p, const NodePtr& fun, const std::vector<NodePtr>& args) {
            return checked(p.applyFun(fun, args), "apply_fun");
        }, py::arg("fun"), py::arg("args"),
           "Apply a defined function (expands the body with the arguments)")
        .def("apply_uf", [](Parser& p, const NodePtr& fun, const std::vector<NodePtr>& args) {
            return checked(p.mkApplyFunc(fun, args), "apply_uf");
        }, py::arg("fun"), py::arg("args"),
           "Apply a function symbol without expanding its body");

    // ---- Transformations & analyses ----
    parser
        .def("substitute", [](Parser& p, const NodePtr& expr,
                              std::unordered_map<std::string, NodePtr> mapping) {
            return checked(p.substitute(expr, mapping), "substitute");
        }, py::arg("expr"), py::arg("mapping"),
           "Substitute variables by name: {var_name: replacement_node}")
        .def("replace_nodes", [](Parser& p, const NodePtr& expr,
                                 std::unordered_map<NodePtr, NodePtr> mapping) {
            return checked(p.replaceNodes(expr, mapping), "replace_nodes");
        }, py::arg("expr"), py::arg("mapping"))
        .def("expand_let", [](Parser& p, const NodePtr& expr) {
            return checked(p.expandLet(expr), "expand_let");
        }, py::arg("expr"), "Eliminate let-bindings by substitution")
        .def("negate_comp", [](Parser& p, const NodePtr& atom) {
            return checked(p.negateComp(atom), "negate_comp");
        }, py::arg("atom"), "Negate a comparison atom (e.g. < becomes >=)")
        .def("converse_comp", [](Parser& p, const NodePtr& atom) {
            return checked(p.converseComp(atom), "converse_comp");
        }, py::arg("atom"),
           "Converse of a comparison atom: swap operands, keep the operator "
           "(a < b becomes b < a, i.e. the reversed relation, NOT equivalent)")
        .def("mirror_comp", [](Parser& p, const NodePtr& atom) {
            return checked(p.mirrorComp(atom), "mirror_comp");
        }, py::arg("atom"),
           "Equivalent mirrored form of a comparison atom: swap operands AND "
           "flip the operator (a < b becomes b > a, same meaning)")
        .def("arith_normalize", [](Parser& p, const NodePtr& expr) {
            return checked(p.arithNormalize(expr), "arith_normalize");
        }, py::arg("expr"))
        .def("binarize_op", [](Parser& p, const NodePtr& expr) {
            return checked(p.binarizeOp(expr), "binarize_op");
        }, py::arg("expr"), "Binarize n-ary operators")
        .def("collect_vars", [](Parser& p, const NodePtr& expr) {
            std::unordered_set<NodePtr> vars;
            p.collectVars(expr, vars);
            return set_to_vector(vars);
        }, py::arg("expr"))
        .def("collect_vars", [](Parser& p, const std::vector<NodePtr>& exprs) {
            std::unordered_set<NodePtr> vars;
            p.collectVars(exprs, vars);
            return set_to_vector(vars);
        }, py::arg("exprs"))
        .def("collect_atoms", [](Parser& p, const NodePtr& expr) {
            std::unordered_set<NodePtr> atoms;
            p.collectAtoms(expr, atoms);
            return set_to_vector(atoms);
        }, py::arg("expr"))
        .def("collect_atoms", [](Parser& p, const std::vector<NodePtr>& exprs) {
            std::unordered_set<NodePtr> atoms;
            p.collectAtoms(exprs, atoms);
            return set_to_vector(atoms);
        }, py::arg("exprs"))
        .def("collect_ground_atoms", [](Parser& p, const std::vector<NodePtr>& exprs) {
            std::unordered_set<NodePtr> atoms;
            p.collectGroundAtoms(exprs, atoms);
            return set_to_vector(atoms);
        }, py::arg("exprs"))
        .def("collect_assignable_vars", [](Parser& p, const NodePtr& expr) {
            std::unordered_set<NodePtr> vars;
            p.collectAssignableVars(expr, vars);
            return set_to_vector(vars);
        }, py::arg("expr"));

    // ---- Normal forms ----
    parser
        .def("to_nnf", [](Parser& p, const NodePtr& expr) {
            return checked(p.toNNF(expr), "to_nnf");
        }, py::arg("expr"))
        .def("to_nnf", [](Parser& p, const std::vector<NodePtr>& exprs) {
            return checked(p.toNNF(exprs), "to_nnf");
        }, py::arg("exprs"))
        .def("to_cnf", [](Parser& p, const NodePtr& expr) {
            return checked(p.toCNF(std::vector<NodePtr>{expr}), "to_cnf");
        }, py::arg("expr"))
        .def("to_cnf", [](Parser& p, const std::vector<NodePtr>& exprs) {
            return checked(p.toCNF(exprs), "to_cnf");
        }, py::arg("exprs"))
        .def("to_dnf", [](Parser& p, const NodePtr& expr) {
            return checked(p.toDNF(expr), "to_dnf");
        }, py::arg("expr"))
        .def("to_dnf", [](Parser& p, const std::vector<NodePtr>& exprs) {
            return checked(p.toDNF(exprs), "to_dnf");
        }, py::arg("exprs"))
        .def("to_tseitin_cnf", [](Parser& p, const NodePtr& expr) {
            std::vector<NodePtr> clauses;
            NodePtr top = p.toTseitinCNF(expr, clauses);
            return py::make_tuple(checked(top, "to_tseitin_cnf"), clauses);
        }, py::arg("expr"),
           "Tseitin CNF; returns (top_literal, clauses)")
        .def("is_cnf", [](Parser& p, const NodePtr& expr) { return p.isCNF(expr); },
            py::arg("expr"))
        .def("is_cnf", [](Parser& p, const std::vector<NodePtr>& exprs) {
            return p.isCNF(exprs);
        }, py::arg("exprs"))
        .def("cnf_atoms", &Parser::getCNFAtoms,
            "Theory atoms abstracted during CNF conversion")
        .def("cnf_bool_vars", &Parser::getCNFBoolVars,
            "Boolean abstraction variables introduced during CNF conversion")
        .def("cnf_atom", [](Parser& p, const NodePtr& bool_var) {
            return opt_node(p.getCNFAtom(bool_var));
        }, py::arg("bool_var"), "Theory atom for a CNF Boolean variable (None if unmapped)")
        .def("cnf_bool_var", [](Parser& p, const NodePtr& atom) {
            return opt_node(p.getCNFBoolVar(atom));
        }, py::arg("atom"), "CNF Boolean variable for a theory atom (None if unmapped)");

    // ---- Evaluation ----
    parser
        .def("evaluate", [](Parser& p, const NodePtr& expr, const ModelPtr& model) {
            if (!model) throw py::value_error("evaluate: model is None");
            auto result = p.evaluate(expr, model);
            if (!result) throw py::value_error("evaluate: evaluation failed");
            return result;
        }, py::arg("expr"), py::arg("model"),
           "Evaluate expr under a (possibly partial) model; returns a node");

    // ---- Output ----
    parser
        .def("to_string", [](Parser& p, const NodePtr& expr) { return p.toString(expr); },
            py::arg("expr"))
        .def("dump_smt2", [](Parser& p) { return p.dumpSMT2(); },
            "Whole parsed content as SMT-LIB2 text")
        .def("dump_smt2", [](Parser& p, const std::string& filename) {
            return p.dumpSMT2(filename);
        }, py::arg("filename"), "Write the parsed content to an SMT-LIB2 file")
        .def("__repr__", [](Parser& p) {
            return "<Parser with " + std::to_string(p.getAssertions().size()) +
                   " assertions>";
        });

    // ===== Module-level convenience functions =====
    m.def("parse", [](const std::string& text) {
        auto p = std::make_shared<Parser>();
        if (!p->parseStr(text)) {
            throw BindParseError("failed to parse SMT-LIB2 input (details on stdout)");
        }
        return p;
    }, py::arg("text"), "Parse SMT-LIB2/OMT text and return the Parser");

    m.def("parse_file", [](const std::string& path) {
        auto p = std::make_shared<Parser>();
        if (!p->parse(path)) {
            throw BindParseError("failed to parse file '" + path + "' (details on stdout)");
        }
        return p;
    }, py::arg("path"), "Parse an SMT-LIB2/OMT file and return the Parser");

    m.attr("__version__") = "0.2.0";

}
