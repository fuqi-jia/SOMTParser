#include "hir_bindings.h"

namespace SomtPythonHir {

void bind(py::module_& m) {
    py::class_<H::Sort>(m, "HirSort")
        .def_static("boolean", &H::Sort::boolean)
        .def_static("integer", &H::Sort::integer)
        .def_static("real", &H::Sort::real)
        .def_static("array", &H::Sort::array)
        .def_static("tuple", &H::Sort::tuple)
        .def_static("uninterpreted", &H::Sort::uninterpreted)
        .def_static("bitvec", &H::Sort::bitvec)
        .def_static("floating", &H::Sort::floating)
        .def_static("string", &H::Sort::string)
        .def_static("reglan", &H::Sort::regLan)
        .def_static("set", &H::Sort::set)
        .def("__repr__", [](const H::Sort& s) { return H::toString(s); });
    m.def("_hir_same_sort", [](const H::Sort& left, const H::Sort& right) {
        return H::sameSort(left, right);
    });
    py::class_<Expr>(m, "HirExpr")
        .def_property_readonly("sort", [](const Expr& e) { return e.value->sort; });

    // Opaque validation-only roots carry their actual lexical environment.
    // No source-name substitution or validation wrapper reaches target SMT.
    py::class_<H::LocatedExpr>(m, "HirSourceTerm");
    m.def("_hir_source_term", [](Expr term, const std::vector<Expr>& environment,
                                  const std::string& source_path) {
        if (!term.value) throw py::value_error("null source validation term");
        std::vector<H::Binder> binders;
        std::unordered_map<std::string, H::Sort> seen;
        for (const auto& binding : environment) {
            if (!binding.value || binding.value->kind != H::ExprKind::BOUND_VAR)
                continue;
            const auto& value = *binding.value;
            const auto inserted = seen.emplace(value.name, value.sort);
            if (!inserted.second) {
                if (!H::sameSort(inserted.first->second, value.sort))
                    throw py::value_error("inconsistent source validation binder sort");
                continue;
            }
            binders.push_back({value.name, value.sort});
        }
        H::ExprPtr expression = term.value;
        if (!binders.empty()) {
            // Equality permits every HIR value sort, without asserting the
            // term's value. Native type checking still visits its full DAG.
            expression = H::mkForall(std::move(binders),
                H::mkOp(H::Op::EQ, {expression, expression}));
        }
        return H::LocatedExpr{std::move(expression), {source_path, 0, 0}};
    }, py::arg("term"), py::arg("environment"), py::arg("source_path"));
    m.def("_hir_const_array", [](const H::Sort& index_sort, Expr value) {
        return Expr{H::mkConstArray(H::Sort::array(index_sort, value.value->sort),
                                   value.value)};
    });
    m.def("_hir_literal", [](const H::Sort& sort, const std::string& text) {
        using K = H::SortKind;
        if (sort.kind == K::BOOL && (text == "true" || text == "false"))
            return Expr{H::mkBool(text == "true")};
        if (sort.kind == K::INT && std::regex_match(text, std::regex("[+-]?[0-9]+")))
            return Expr{H::mkInt(text)};
        if (sort.kind == K::REAL && std::regex_match(text, std::regex("[+-]?[0-9]+(\\.[0-9]+|/[1-9][0-9]*)?")))
            return Expr{H::mkReal(text)};
        if (sort.kind == K::STRING)
            return Expr{H::mkString(text)};
        if (sort.kind == K::REGLAN
            && (text == "re.none" || text == "re.all" || text == "re.allchar"))
            return Expr{H::mkReglanConst(text)};
        if (sort.kind == K::SET && (text == "set.empty" || text == "set.universe"))
            return Expr{H::mkSetConst(text, sort)};
        if (sort.kind == K::BITVEC) {
            // The text carries its own width; a literal that disagreed with
            // the declared sort would be zero-extended or truncated without a
            // diagnostic by the engine's builder, so it is refused here.
            if (text.size() > 2 && text[0] == '#' && text[1] == 'b'
                && text.find_first_not_of("01", 2) == std::string::npos
                && text.size() - 2 == sort.width)
                return Expr{H::mkBitVec(text, sort.width)};
            if (text.size() > 2 && text[0] == '#' && text[1] == 'x'
                && text.find_first_not_of("0123456789abcdefABCDEF", 2) == std::string::npos
                && 4 * (text.size() - 2) == sort.width)
                return Expr{H::mkBitVec(text, sort.width)};
            throw py::value_error("bit-vector literal width does not match its sort");
        }
        if (sort.kind == K::FLOAT) {
            // The three spellings hir/typecheck.h accepts: a decimal (emitted
            // as a to_fp conversion), one of the five special values, and the
            // bit triple -- each tied to the literal's own format.
            static const std::regex kDecimal(R"(^[+-]?\d+(\.\d+)?$)");
            static const std::regex kSpecial(R"(^\(_ (\+oo|-oo|\+zero|-zero|NaN) (\d+) (\d+)\)$)");
            static const std::regex kTriple(R"(^\(fp #b([01]+) #b([01]+) #b([01]+)\)$)");
            std::smatch fields;
            if (std::regex_match(text, kDecimal))
                return Expr{H::mkFloat(text, sort.exponent_bits, sort.significand_bits)};
            if (std::regex_match(text, fields, kSpecial)
                && fields[2].str() == std::to_string(sort.exponent_bits)
                && fields[3].str() == std::to_string(sort.significand_bits))
                return Expr{H::mkFloat(text, sort.exponent_bits, sort.significand_bits)};
            if (std::regex_match(text, fields, kTriple)
                && fields[1].length() == 1
                && static_cast<unsigned>(fields[2].length()) == sort.exponent_bits
                && static_cast<unsigned>(fields[3].length()) + 1 == sort.significand_bits)
                return Expr{H::mkFloat(text, sort.exponent_bits, sort.significand_bits)};
            throw py::value_error("invalid floating-point literal for its format");
        }
        throw py::value_error("unsupported HIR literal");
    });
    m.def("_hir_rounding_mode", [](const std::string& mode) {
        static const std::unordered_set<std::string> modes =
            {"RNE", "RNA", "RTP", "RTN", "RTZ"};
        if (!modes.count(mode)) throw py::value_error("unknown rounding mode: " + mode);
        return Expr{H::mkRoundingMode(mode)};
    });
    m.def("_hir_ident", [](std::string n, H::Sort s, bool bound) {
        if (n.empty()) throw py::value_error("empty identifier");
        return Expr{bound ? H::mkBoundVar(n, s) : H::mkIdent(n, s)};
    });
    m.def("_hir_tuple_unit", []() { return Expr{H::mkTupleUnit()}; });
    m.def("_hir_tuple", [](const std::vector<Expr>& fields) {
        if (fields.empty())
            throw py::value_error("tuple constructor requires at least one field; use tuple_unit");
        return Expr{H::mkTuple(values(fields))};
    });
    m.def("_hir_tuple_op", [](const std::string& op,
                               const std::vector<long long>& indices,
                               const std::vector<Expr>& args) {
        const bool project = op == "tuple.project";
        const bool select = op == "tuple.select";
        const bool update = op == "tuple.update";
        if (!project && !select && !update)
            throw py::value_error("unknown indexed tuple operator: " + op);
        if ((project && args.size() != 1) || (select && (indices.size() != 1 || args.size() != 1))
            || (update && (indices.size() != 1 || args.size() != 2)))
            throw py::value_error("invalid tuple operator index or argument arity: " + op);
        if (args.empty() || args[0].value->sort.kind != H::SortKind::TUPLE)
            throw py::value_error("tuple operator requires a tuple operand: " + op);
        const auto& fields = args[0].value->sort.args;
        std::vector<unsigned> checked;
        checked.reserve(indices.size());
        for (long long index : indices) {
            if (index < 0 || static_cast<unsigned long long>(index) > std::numeric_limits<unsigned>::max())
                throw py::value_error("tuple index is outside the supported range");
            const auto field = static_cast<std::size_t>(index);
            if (field >= fields.size() || !fields[field])
                throw py::value_error("tuple index out of range: " + std::to_string(index));
            checked.push_back(static_cast<unsigned>(index));
        }
        if (update && !H::sameSort(args[1].value->sort, *fields[checked[0]]))
            throw py::value_error("tuple.update replacement sort does not match selected field");
        if (select) return Expr{H::mkTupleSelect(args[0].value, checked[0])};
        if (update) return Expr{H::mkTupleUpdate(args[0].value, checked[0], args[1].value)};
        return Expr{H::mkTupleProject(args[0].value, std::move(checked))};
    });
    m.def("_hir_op", [](const std::string& op, const std::vector<Expr>& args) {
        struct OpSpec { H::Op op; std::size_t min_args; std::size_t max_args; };
        const std::size_t nary = std::numeric_limits<std::size_t>::max();
        static const std::unordered_map<std::string, OpSpec> ops = {
            {"and", {H::Op::AND, 2, 0}}, {"or", {H::Op::OR, 2, 0}},
            {"not", {H::Op::NOT, 1, 1}},
            {"eq", {H::Op::EQ, 2, 0}}, {"le", {H::Op::LE, 2, 0}},
            {"lt", {H::Op::LT, 2, 0}},
            {"ge", {H::Op::GE, 2, 0}}, {"gt", {H::Op::GT, 2, 0}},
            {"add", {H::Op::ADD, 2, 0}},
            {"sub", {H::Op::SUB, 2, 2}}, {"mul", {H::Op::MUL, 2, 0}},
            {"div", {H::Op::DIV_REAL, 2, 2}},
            {"div_euclid", {H::Op::DIV_EUCLID, 2, 2}},
            {"div_trunc", {H::Op::DIV_TRUNC, 2, 2}},
            {"div_floor", {H::Op::DIV_FLOOR, 2, 2}},
            {"mod_euclid", {H::Op::MOD_EUCLID, 2, 2}},
            {"mod_trunc", {H::Op::MOD_TRUNC, 2, 2}},
            {"mod_floor", {H::Op::MOD_FLOOR, 2, 2}},
            {"implies", {H::Op::IMPLIES, 2, 2}}, {"xor", {H::Op::XOR, 2, 0}},
            {"ite", {H::Op::ITE, 3, 3}}, {"distinct", {H::Op::DISTINCT, 2, 0}},
            {"select", {H::Op::SELECT, 2, 2}}, {"store", {H::Op::STORE, 3, 3}},
            {"array.map.and", {H::Op::ARRAY_MAP_AND, 2, 0}},
            {"array.map.or", {H::Op::ARRAY_MAP_OR, 2, 0}},
            {"array.map.not", {H::Op::ARRAY_MAP_NOT, 1, 1}},
            // Bit-vectors: n-ary where SMT-LIB is (the associative group and
            // concat), binary elsewhere, the two negations unary.
            {"bvnot", {H::Op::BV_NOT, 1, 1}}, {"bvneg", {H::Op::BV_NEG, 1, 1}},
            {"bvand", {H::Op::BV_AND, 2, 0}}, {"bvor", {H::Op::BV_OR, 2, 0}},
            {"bvxor", {H::Op::BV_XOR, 2, 0}},
            {"bvadd", {H::Op::BV_ADD, 2, 0}}, {"bvmul", {H::Op::BV_MUL, 2, 0}},
            {"bvudiv", {H::Op::BV_UDIV, 2, 2}},
            {"bvurem", {H::Op::BV_UREM, 2, 2}},
            {"bvshl", {H::Op::BV_SHL, 2, 2}}, {"bvlshr", {H::Op::BV_LSHR, 2, 2}},
            {"bvashr", {H::Op::BV_ASHR, 2, 2}},
            {"bvult", {H::Op::BV_ULT, 2, 2}}, {"bvule", {H::Op::BV_ULE, 2, 2}},
            {"bvugt", {H::Op::BV_UGT, 2, 2}}, {"bvuge", {H::Op::BV_UGE, 2, 2}},
            {"bvslt", {H::Op::BV_SLT, 2, 2}}, {"bvsle", {H::Op::BV_SLE, 2, 2}},
            {"bvsgt", {H::Op::BV_SGT, 2, 2}}, {"bvsge", {H::Op::BV_SGE, 2, 2}},
            {"concat", {H::Op::BV_CONCAT, 2, 0}},
            // Floating point: the arithmetic group takes the rounding mode as
            // its first argument; fp.eq is IEEE equality, not structural =.
            {"fp.eq", {H::Op::FP_EQ, 2, 2}}, {"fp.lt", {H::Op::FP_LT, 2, 2}},
            {"fp.leq", {H::Op::FP_LEQ, 2, 2}}, {"fp.gt", {H::Op::FP_GT, 2, 2}},
            {"fp.geq", {H::Op::FP_GEQ, 2, 2}},
            {"fp.add", {H::Op::FP_ADD, 3, 3}}, {"fp.sub", {H::Op::FP_SUB, 3, 3}},
            {"fp.mul", {H::Op::FP_MUL, 3, 3}}, {"fp.div", {H::Op::FP_DIV, 3, 3}},
            {"fp.abs", {H::Op::FP_ABS, 1, 1}}, {"fp.neg", {H::Op::FP_NEG, 1, 1}},
            // Strings, minus the regular-expression fragment.
            {"str.++", {H::Op::STR_CONCAT, 2, 0}},
            {"str.len", {H::Op::STR_LEN, 1, 1}},
            {"str.at", {H::Op::STR_AT, 2, 2}},
            {"str.contains", {H::Op::STR_CONTAINS, 2, 2}},
            {"str.prefixof", {H::Op::STR_PREFIXOF, 2, 2}},
            {"str.suffixof", {H::Op::STR_SUFFIXOF, 2, 2}},
            {"str.indexof", {H::Op::STR_INDEXOF, 3, 3}},
            {"str.substr", {H::Op::STR_SUBSTR, 3, 3}},
            {"str.replace", {H::Op::STR_REPLACE, 3, 3}},
            {"str.to_int", {H::Op::STR_TO_INT, 1, 1}},
            {"str.from_int", {H::Op::STR_FROM_INT, 1, 1}},
            {"str.to_re", {H::Op::STR_TO_RE, 1, 1}},
            {"str.in_re", {H::Op::STR_IN_RE, 2, 2}},
            {"re.++", {H::Op::RE_CONCAT, 2, 0}},
            {"re.union", {H::Op::RE_UNION, 2, 0}},
            {"re.inter", {H::Op::RE_INTER, 2, 0}},
            {"re.diff", {H::Op::RE_DIFF, 2, 2}},
            {"re.*", {H::Op::RE_STAR, 1, 1}},
            {"re.+", {H::Op::RE_PLUS, 1, 1}},
            {"re.opt", {H::Op::RE_OPT, 1, 1}},
            {"re.comp", {H::Op::RE_COMPLEMENT, 1, 1}},
            {"re.range", {H::Op::RE_RANGE, 2, 2}},
            {"set.singleton", {H::Op::SET_SINGLETON, 1, 1}},
            {"set.union", {H::Op::SET_UNION, 2, 0}},
            {"set.inter", {H::Op::SET_INTER, 2, 0}},
            {"set.minus", {H::Op::SET_MINUS, 2, 2}},
            {"set.insert", {H::Op::SET_INSERT, 2, 0}},
            {"set.member", {H::Op::SET_MEMBER, 2, 2}},
            {"set.subset", {H::Op::SET_SUBSET, 2, 2}},
            {"set.card", {H::Op::SET_CARD, 1, 1}},
            {"set.complement", {H::Op::SET_COMPLEMENT, 1, 1}},
        };
        auto it = ops.find(op);
        if (it == ops.end()) throw py::value_error("unknown HIR operator: " + op);
        const auto n = args.size();
        const auto max = it->second.max_args ? it->second.max_args : nary;
        if (n < it->second.min_args || n > max)
            throw py::value_error("invalid HIR operator arity");
        // mkOp derives result sorts before typeCheck; enforce array shape here.
        if ((op == "select" || op == "store") && args[0].value->sort.kind != H::SortKind::ARRAY)
            throw py::value_error("array operand required");
        if (op == "array.map.and" || op == "array.map.or" || op == "array.map.not") {
            for (const auto& arg : args) {
                const auto& sort = arg.value->sort;
                if (sort.kind != H::SortKind::ARRAY || !sort.elem
                    || sort.elem->kind != H::SortKind::BOOL
                    || !H::sameSort(sort, args[0].value->sort))
                    throw py::value_error("Boolean array map requires identical Boolean array sorts");
            }
        }
        // These builders feed native parser constructors, some of which report
        // wrong sorts through an unknown node instead of a Python exception.
        // Refuse bad signatures before constructing them.
        const auto kind = [&](std::size_t i) { return args[i].value->sort.kind; };
        if ((op == "str.to_re" && kind(0) != H::SortKind::STRING)
            || (op == "str.in_re" && (kind(0) != H::SortKind::STRING
                                       || kind(1) != H::SortKind::REGLAN))
            || (op == "re.range" && (kind(0) != H::SortKind::STRING
                                      || kind(1) != H::SortKind::STRING))
            || ((op == "re.++" || op == "re.union" || op == "re.inter"
                 || op == "re.diff" || op == "re.*" || op == "re.+"
                 || op == "re.opt" || op == "re.comp")
                && std::any_of(args.begin(), args.end(), [&](const Expr& e) {
                    return e.value->sort.kind != H::SortKind::REGLAN;
                })))
            throw py::value_error("regular-expression operand sort mismatch: " + op);
        const auto is_set = [&](std::size_t i) {
            return kind(i) == H::SortKind::SET && args[i].value->sort.elem;
        };
        if (op == "set.card" || op == "set.complement") {
            if (!is_set(0)) throw py::value_error("set operand required: " + op);
        } else if (op == "set.member") {
            if (!is_set(1)
                || !H::sameSort(args[0].value->sort, *args[1].value->sort.elem))
                throw py::value_error("set.member element/set sort mismatch");
        } else if (op == "set.union" || op == "set.inter"
                   || op == "set.minus" || op == "set.subset") {
            if (!is_set(0)) throw py::value_error("set operands required: " + op);
            for (const auto& arg : args) {
                if (arg.value->sort.kind != H::SortKind::SET
                    || !H::sameSort(arg.value->sort, args[0].value->sort))
                    throw py::value_error("set operands must have one exact sort: " + op);
            }
        } else if (op == "set.insert") {
            const auto& set = args.back().value->sort;
            if (set.kind != H::SortKind::SET || !set.elem)
                throw py::value_error("set.insert requires a set as its last argument");
            for (std::size_t i = 0; i + 1 < args.size(); ++i) {
                if (!H::sameSort(args[i].value->sort, *set.elem))
                    throw py::value_error("set.insert element/set sort mismatch");
            }
        }
        return Expr{H::mkOp(it->second.op, values(args))};
    });
    m.def("_hir_op_indexed", [](const std::string& op,
                                const std::vector<long long>& indices,
                                const std::vector<Expr>& args) {
        // Indexed operators: the indices name WHICH function is applied, so
        // they route to the dedicated checked builders rather than mkOp, whose
        // signature has nowhere to put them. Index counts and arities are
        // validated here; width relations are Uir::Hir::typeCheck's business.
        for (long long i : indices) {
            if (i < 0 || i > 0xFFFFFFFFLL)
                throw py::value_error("invalid index for indexed HIR operator: " + op);
        }
        auto at = [&indices](std::size_t k) {
            return static_cast<unsigned>(indices[k]);
        };
        auto shape = [&op, &indices, &args](std::size_t ni, std::size_t na) {
            if (indices.size() != ni || args.size() != na)
                throw py::value_error("invalid index or argument count for: " + op);
        };
        if (op == "extract") {
            shape(2, 1);
            return Expr{H::mkBvExtract(args[0].value, at(0), at(1))};
        }
        if (op == "zero_extend" || op == "sign_extend") {
            shape(1, 1);
            return Expr{H::mkBvExtend(op == "zero_extend" ? H::Op::BV_ZERO_EXTEND
                                                          : H::Op::BV_SIGN_EXTEND,
                                      args[0].value, at(0))};
        }
        if (op == "rotate_left" || op == "rotate_right") {
            shape(1, 1);
            return Expr{H::mkBvRotate(op == "rotate_left" ? H::Op::BV_ROTATE_LEFT
                                                          : H::Op::BV_ROTATE_RIGHT,
                                      args[0].value, at(0))};
        }
        if (op == "repeat") {
            shape(1, 1);
            return Expr{H::mkBvRepeat(args[0].value, at(0))};
        }
        if (op == "int2bv") {
            shape(1, 1);
            return Expr{H::mkIntToBv(args[0].value, at(0))};
        }
        if (op == "divisible") {
            shape(1, 1);
            return Expr{H::mkIsDivisible(args[0].value, at(0))};
        }
        if (op == "re.loop") {
            shape(2, 1);
            if (args[0].value->sort.kind != H::SortKind::REGLAN)
                throw py::value_error("re.loop requires a RegLan operand");
            return Expr{H::mkReLoop(args[0].value, at(0), at(1))};
        }
        if (op == "fp.to_sbv" || op == "fp.to_ubv") {
            shape(1, 2);
            return Expr{H::mkFpToBv(op == "fp.to_sbv" ? H::Op::FP_TO_SBV
                                                      : H::Op::FP_TO_UBV,
                                    args[0].value, args[1].value, at(0))};
        }
        if (op == "to_fp" || op == "to_fp_unsigned") {
            shape(2, 2);
            return Expr{H::mkToFp(op == "to_fp" ? H::Op::TO_FP
                                                : H::Op::TO_FP_UNSIGNED,
                                  args[0].value, args[1].value, at(0), at(1))};
        }
        if (op == "ieee_bv_to_fp") {
            shape(2, 1);
            return Expr{H::mkIeeeBvToFp(args[0].value, at(0), at(1))};
        }
        throw py::value_error("unknown indexed HIR operator: " + op);
    });
    m.def("_hir_apply", [](std::string n, H::Sort result, const std::vector<Expr>& args) {
        if (n.empty()) throw py::value_error("empty function name");
        return Expr{H::mkApply(n, result, values(args))};
    });
    m.def("_hir_quantifier", [](bool universal,
              const std::vector<std::pair<std::string, H::Sort>>& bindings, Expr body) {
        std::vector<H::Binder> binders;
        if (bindings.empty()) throw py::value_error("quantifier requires binders");
        for (const auto& b : bindings) binders.push_back({b.first, b.second});
        return Expr{universal ? H::mkForall(binders, body.value) : H::mkExists(binders, body.value)};
    });
    m.def("_hir_sort_datatype", [](const std::string& name,
                                      const std::vector<H::Sort>& args) {
        if (name.empty()) throw py::value_error("empty datatype sort name");
        return H::Sort::datatype(name, args);
    });
    m.def("_hir_sort_parameter", [](const std::string& name) {
        if (name.empty()) throw py::value_error("empty datatype parameter name");
        return H::Sort::uninterpreted(name);
    });
    m.def("_hir_dt_constructor", [](std::string name, H::Sort result,
                                      const std::vector<Expr>& args) {
        if (name.empty()) throw py::value_error("empty datatype constructor name");
        return Expr{H::mkDtConstructor(std::move(name), std::move(result), values(args))};
    });
    m.def("_hir_dt_selector", [](std::string name, H::Sort result, Expr value) {
        if (name.empty()) throw py::value_error("empty datatype selector name");
        return Expr{H::mkDtSelector(std::move(name), std::move(result), value.value)};
    });
    m.def("_hir_dt_tester", [](std::string constructor, Expr value) {
        if (constructor.empty()) throw py::value_error("empty datatype constructor name");
        return Expr{H::mkDtTester(std::move(constructor), value.value)};
    });
    m.def("_hir_declare_datatypes", [](H::ConstraintModel& model,
                 const std::vector<std::tuple<std::string, std::vector<std::string>,
                     std::vector<std::pair<std::string,
                         std::vector<std::pair<std::string, H::Sort>>>>, bool>>& declarations) {
        std::vector<H::DatatypeDecl> staged;
        staged.reserve(declarations.size());
        for (const auto& source : declarations) {
            H::DatatypeDecl declaration;
            declaration.name = std::get<0>(source);
            declaration.params = std::get<1>(source);
            declaration.coinductive = std::get<3>(source);
            for (const auto& constructor : std::get<2>(source)) {
                H::DtConstructor out;
                out.name = constructor.first;
                for (const auto& selector : constructor.second) {
                    out.selectors.push_back({selector.first, selector.second});
                }
                declaration.constructors.push_back(std::move(out));
            }
            staged.push_back(std::move(declaration));
        }
        model.datatypes.insert(model.datatypes.end(), staged.begin(), staged.end());
    });
    m.def("_hir_global", [](std::string name, const std::vector<Expr>& args) {
        if (name.empty()) throw py::value_error("empty global name");
        return Expr{H::mkGlobal(name, values(args))};
    });
    py::class_<H::ConstraintModel>(m, "HirModel")
        .def(py::init<>())
        .def("declare", [](H::ConstraintModel& m, std::string n, H::Sort s,
                           const std::string& source_path) {
            if (n.empty()) throw py::value_error("empty declaration name");
            m.decls.push_back({n, s, nullptr, nullptr, {}});
            m.decls.back().loc.file = source_path;
            return Expr{H::mkIdent(n, s)};
        }, py::arg("name"), py::arg("sort"), py::kw_only(),
           py::arg("source_path") = "")
        .def("declare_function", [](H::ConstraintModel& m, std::string n,
                                     std::vector<H::Sort> args, H::Sort result,
                                     bool auxiliary, const std::string& source_path) {
            m.funs.push_back({n, args, result, {}});
            m.funs.back().auxiliary = auxiliary;
            m.funs.back().loc.file = source_path;
        }, py::arg("name"), py::arg("arguments"), py::arg("result"),
           py::kw_only(), py::arg("auxiliary") = false, py::arg("source_path") = "")
        .def("define_function", [](H::ConstraintModel& m, const std::string& n,
                                    const std::vector<std::pair<std::string, H::Sort>>& binders,
                                    Expr body, const std::string& source_path) {
            auto found = std::find_if(m.funs.begin(), m.funs.end(),
                [&](const H::FunDecl& function) { return function.name == n; });
            if (found == m.funs.end())
                throw py::value_error("cannot define an undeclared function: " + n);
            if (found->body)
                throw py::value_error("function already has a definition: " + n);
            found->binders.clear();
            found->binders.reserve(binders.size());
            for (const auto& binder : binders)
                found->binders.push_back({binder.first, binder.second});
            found->body = body.value;
            found->loc.file = source_path;
        }, py::arg("name"), py::arg("binders"), py::arg("body"), py::kw_only(),
           py::arg("source_path") = "")
        .def("constrain", [](H::ConstraintModel& m, Expr e, const std::string& source_path) {
            H::Constraint c; c.formula = e.value; c.loc.file = source_path;
            m.constraints.push_back(c);
        }, py::arg("expr"), py::kw_only(), py::arg("source_path") = "")
        .def("soft_constrain", [](H::ConstraintModel& m, Expr e,
                                  py::str weight_value, py::str group_value,
                                  const std::string& source_path) {
            const std::string weight = weight_value.cast<std::string>();
            const std::string group = group_value.cast<std::string>();
            if (!e.value || e.value->sort.kind != H::SortKind::BOOL)
                throw py::value_error("soft constraint formula must be Bool");
            if (!H::isExactPositiveSoftWeight(weight))
                throw py::value_error("soft weight must be a positive integer decimal string");
            if (!H::isSoftGroupSymbol(group))
                throw py::value_error("soft group must be empty or a valid SMT-LIB symbol spelling");
            H::Constraint constraint;
            constraint.formula = e.value;
            constraint.soft = true;
            // Canonicalize leading zeroes without any machine-number conversion.
            constraint.weight_text = weight.substr(weight.find_first_not_of('0'));
            constraint.group = group;
            constraint.loc.file = source_path;
            m.constraints.push_back(std::move(constraint));
        }, py::arg("expr"), py::arg("weight").noconvert(), py::kw_only(),
           py::arg("group").noconvert() = "", py::arg("source_path") = "",
           "Add one soft Bool constraint with exact positive integer weight. Equal groups "
           "sum violation costs; groups follow first appearance, before explicit objectives. "
           "Multiple effective objectives require an explicit objective_order.")
        .def("objective", [](H::ConstraintModel& m, bool maximize, Expr e,
                             const std::string& source_path) {
            m.objectives.push_back({maximize ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE, e.value, "", {}});
            m.objectives.back().loc.file = source_path;
        }, py::arg("maximize"), py::arg("expr"), py::kw_only(),
           py::arg("source_path") = "")
        .def("objective_order", [](H::ConstraintModel& m, const std::string& order) {
            if (order == "single") m.objective_combination = H::ObjectiveCombination::SINGLE;
            else if (order == "lexicographic") m.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
            else throw py::value_error("unsupported objective order");
        })
        .def("validate", [](const H::ConstraintModel& model,
                            const std::vector<H::LocatedExpr>& source_terms) {
            // Use the same checker as translateHir without running any pass,
            // target lowering, serialization, or solver.
            SOMTParser::Uir::Diagnostics diagnostics;
            if (source_terms.empty()) H::typeCheck(model, diagnostics);
            else H::typeCheckTerms(model, source_terms, diagnostics);
            return diagnostics.all();
        }, py::arg("source_terms") = std::vector<H::LocatedExpr>{})
        .def("translate", [](const H::ConstraintModel& model, const std::string& profile,
                             SOMTParser::Lower::OmtDialect dialect,
                             const std::vector<H::LocatedExpr>& source_terms, bool details) {
            SOMTParser::TranslateOptions options;
            options.details = details;
            options.profile_id = profile; options.omt_dialect = dialect;
            return SOMTParser::translate(model, options, source_terms);
        }, py::arg("profile") = "default", py::arg("dialect") = SOMTParser::Lower::OmtDialect::Z3,
           py::kw_only(), py::arg("source_terms") = std::vector<H::LocatedExpr>{}, py::arg("details") = true);
}

} // namespace SomtPythonHir
