"""Source-linked construction examples for natural-language HIR providers."""

MODELING_GUIDANCE = (
    'Distinguish constants from variable references: {"literal": "15", "sort": "Real"} '
    'is an exact Real constant, while {"var": "x"} is the declared quantity x. '
    'Whole-number Real constants still use strings; do not use a JSON number or '
    'put a variable name in literal. A source coefficient of one can be omitted '
    '(use the variable directly) or encoded as {"literal": "1", "sort": "Real"}. '
    'For 3*x, multiply the exact constant "3" by the variable x, never literal "x" '
    'by x. Check every factor against the source; a construction diagnostic does '
    'not authorize replacing a bad coefficient with a variable or guessing its value. '
    "Keep exact fractions as rational Real literals such as '1/7', never as rounded "
    "finite decimals unless the source specifies that approximation. For a percentage "
    "of a total, first identify all terms in that total: 'A is at least p percent of "
    "A and B combined' means A >= (p/100)*(A+B), not A >= (p/100)*B. Keep the "
    "unsimplified part-versus-total form when constructing the model to avoid "
    "reversing coefficients. Use the source/context's numeric domain; a percentage "
    "does not itself require integers or imply a positive total. If the source "
    "instead defines a ratio A/total, preserve its denominator-definedness condition. "
    "Repeated comparisons of the same numeric attribute must refer to one Int/Real "
    "value or function, with the stated units and exact thresholds. Do not model "
    "below/above thresholds as unrelated Boolean predicates, or replace above with "
    "not-below: equality is a separate boundary case. Use Int only for a discrete "
    "quantity supported by the source. "
    "Array shape specifies index coordinates, not the values stored at those coordinates. "
    "Encode every stated element domain explicitly: use inclusive declaration lower/upper "
    "bounds for a uniform Int/Real domain, or add per-element constraints when domains vary. "
    "For entries stated to be integers from 0 to m-1, use lower=0 and upper=m-1; "
    "shape=[m,m] and all_different alone leave element values unbounded. "
    "When a stored value is later used as an index, preserve its source domain as well; "
    "SMT array access remains defined outside the declared finite shape. "
    "Represent generic categories by predicates and quantified rules, and named "
    "individuals by constants. Preserve category guards; assert membership only "
    "when stated or entailed by the source/context. Never invent a membership fact "
    "just to activate a guarded rule. A universal rule does not assert that its "
    "category has members, even though the underlying first-order sort is nonempty. "
    "Inclusive or allows both alternatives; exactly-one excludes both being true. "
    "Use the source/context to determine which is intended, retaining a genuine "
    "unsettled reading in unresolved. Do not add exclusivity, existential import, "
    "unique names, or background facts merely to obtain a definite conclusion. "
    "Use the optional interpretation_notes string array for explanations of the interpretation "
    "already encoded in declarations and constraints. Notes add no constraints and must not replace "
    "source requirements. Record explicitly applied modeling conventions in assumptions; keep "
    "genuinely competing readings in unresolved. Never move an unresolved alternative into notes "
    "merely to allow compilation. No field automatically resolves ambiguity. "
    "For an unresolved item, identify the exact source phrase and the competing readings that change the relation; "
    "an explanation that an explicit existence statement uses an existential quantifier is an interpretation note, "
    "not itself a competing reading. Preserve genuine scope or existence alternatives. "
    "Read coordination at its grammatical level: a list of categories such as 'all violinists and drummers' "
    "can distribute a rule over both categories; 'people who are both violinists and drummers' describes their intersection. "
    "Do not apply either pattern without checking the actual modifiers and source context. "
    "For 'neither A nor B', negate the two complete coordinated propositions. If B contains a conjunction, "
    "not(B1 and B2) is not the same as not(B1) and not(B2). Check relative-clause attachment and negation scope "
    "before choosing an encoding; report a genuine unresolved attachment instead of silently strengthening it. "
    "Distinguish an entity's identifier from the entity stored at a row index. When the source requests "
    "one list per category, in a specified entity order, and equal values identify associated entities, "
    "each list maps that category's entities to shared identifiers. Encode association by equality of "
    "the corresponding entries; do not silently return row-aligned category codes, which are the inverse "
    "representation. Preserve all identifier permutations unless the source fixes an ordering. "
    "Count distinct used labels when the source defines that objective. A maximum label is generally "
    "a different pointwise cost, even when minimizing it can find the same optimum after relabeling. "
    "Use the stated label domain and exact cost definition; do not add contiguity or canonical-label "
    "constraints to make the two costs coincide. "
    "Before changing units, distinguish each input number's unit, the unit of the declared variable, "
    "and the required output and objective units. A unit conversion does not make a Real quantity "
    "discrete: monetary amounts do not imply whole cents, and lengths do not imply whole millimetres. "
    "Use Int, rounding, or a fixed precision only when the source or explicit context requires it. "
    "Use exact rational conversion factors. If q_out = scale*q_in, a sum of quantities with that "
    "common scale changes by scale, but a product of n quantities changes by scale^n; with distinct "
    "scales the product changes by their product. For example, converting every metre-valued edge "
    "to millimetres multiplies a three-edge volume by 1000^3, while an area changes by 1000^2. "
    "Translate every side of each equality and inequality in its own dimensions, and convert the "
    "pointwise objective value back to its requested unit, not merely to a cost with the same optimum. "
    "Preserve the source's signs, strictness, ordering freedom and domains. Do not invent sorting, "
    "positivity, upper bounds, or integrality to simplify solving or repair a scaling error. "
    "The constructor catalog's modeling_patterns are independent worked examples; "
    "adapt the construction to the actual source, without copying their names or spans."
)


def modeling_patterns():
    """Return fresh, complete examples usable through the ordinary HIR API."""
    entity = {"Uninterpreted": "Entity"}

    def apply(name, argument):
        return {"apply": name, "args": [{"var": argument}]}

    def op(name, *arguments):
        return {"op": name, "args": list(arguments)}

    def quantify(kind, body):
        return {"quantifier": kind, "binders": [{"name": "x", "sort": entity}],
                "body": body}

    def example(statements, expressions, declarations, functions, explanation, *, goal=True):
        source = "\n".join(statements)
        constraints = []
        offset = 0
        for statement, expression in zip(statements, expressions):
            constraints.append({"expr": expression,
                                "span": [offset, offset + len(statement)]})
            offset += len(statement) + 1
        return {
            "explanation": explanation,
            "source": source,
            "model": {
                "schema": "somt-hir-model-v1", "language": "hir",
                "decision": "satisfiability",
                "declarations": declarations + ([{"name": "somt_goal", "sort": "Bool"}] if goal else []),
                "functions": functions, "constraints": constraints,
                "objectives": [], "objective_order": "single", "goal": None,
                "assumptions": [], "unresolved": [],
            },
        }

    temperature = apply("temperature", "rho")
    threshold = {"literal": "5", "sort": "Real"}
    rule = quantify("forall", op("implies", apply("glider", "x"), apply("light", "x")))
    predicates = [{"name": name, "arguments": [entity], "result": "Bool"}
                  for name in ("glider", "light")]
    resin, filler = {"var": "resin"}, {"var": "filler"}
    load, reserve = {"var": "load"}, {"var": "reserve"}
    zero = {"literal": "0", "sort": "Real"}

    def integer(value):
        return {"literal": value, "sort": "Int"}

    def cell(name, index):
        return {"at": name, "indices": [integer(index)]}

    shared_ids = example(
        ["Output riders in the order Ada, Bela, Ciro and bikes in the order amber, black, cyan.",
         "Each list is a permutation of the shared identifiers 1, 2, 3; equal identifiers associate a rider and a bike.",
         "Ada rides the cyan bike."],
        [op("and"),
         op("and", op("all_different", {"var": "riders"}),
            op("all_different", {"var": "bikes"})),
         op("eq", cell("riders", 0), cell("bikes", 2))],
        [{"name": name, "sort": "Int", "shape": [3], "lower": 1, "upper": 3}
         for name in ("riders", "bikes")], [],
        "List indices name entities in the given order; values are shared identifiers. "
        "Ada and cyan have the same value, not necessarily value 1 or value 3. "
        "No identifier permutation is preferred.", goal=False)

    distinct_labels = example(
        ["Assign each of three jobs a label from the integers 2 through 5, output as labels in job order.",
         "The first and second jobs must have different labels.",
         "Minimize the number of distinct labels used by the jobs."],
        [op("and"), op("ne", cell("labels", 0), cell("labels", 1)), op("and")],
        [{"name": "labels", "sort": "Int", "shape": [3], "lower": 2, "upper": 5}], [],
        "Each allowed label contributes one exactly when some job uses it. The maximum "
        "label and the count of distinct labels need not agree; no label-contiguity restriction is added.",
        goal=False)
    distinct_labels["model"]["decision"] = "optimization"
    distinct_labels["model"]["objectives"] = [{
        "sense": "minimize",
        "expr": op("count", *[
            op("or", *[op("eq", cell("labels", i), integer(label)) for i in range(3)])
            for label in range(2, 6)]),
        "span": distinct_labels["model"]["constraints"].pop()["span"],
    }]
    def real(value):
        return {"literal": value, "sort": "Real"}

    money_units = example(
        ["Let invoice_dollars and rebate_dollars be real adjustment amounts in dollars; signed amounts and fractional cents are allowed.",
         "Report net_cents, the invoice adjustment minus the rebate adjustment, in cents; one dollar is exactly 100 cents."],
        [op("and"), op("eq", {"var": "net_cents"},
             op("mul", real("100"), op("sub", {"var": "invoice_dollars"}, {"var": "rebate_dollars"})))],
        [{"name": name, "sort": "Real"}
         for name in ("invoice_dollars", "rebate_dollars", "net_cents")], [],
        "The input amounts remain dollar-valued Reals; only the reported difference is in cents. "
        "No rounding, whole-cent restriction, sign bound, or ordering of adjustments is imposed.",
        goal=False)
    money_units["required_outputs"] = [{"name": "net_cents", "sort": "Real", "shape": []}]

    edges = [cell("edges_mm", i) for i in range(3)]
    cavity_units = example(
        ["A rectangular sensor cavity has three positive real edge lengths u, v, w in metres.",
         "Its volume u*v*w is exactly 7/250 cubic metres.",
         "Report the three lengths as edges_mm in u, v, w order, in millimetres; one metre is exactly 1000 millimetres.",
         "Report surface_area_m2 in square metres, equal to twice (u*v + u*w + v*w).",
         "Minimize surface_area_m2."],
        [op("and", *[op("gt", edge, real("0")) for edge in edges]),
         op("eq", op("mul", *edges), real("28000000")),
         op("and"),
         op("eq", {"var": "surface_area_m2"},
            op("mul", real("1/500000"),
               op("add", op("mul", edges[0], edges[1]),
                  op("mul", edges[0], edges[2]), op("mul", edges[1], edges[2])))),
         op("and")],
        [{"name": "edges_mm", "sort": "Real", "shape": [3]},
         {"name": "surface_area_m2", "sort": "Real"}], [],
        "The edge variables store millimetres, so volume scales by 1000^3: "
        "(7/250)*1000^3 = 28000000. The pairwise products scale by 1000^2; "
        "multiplying their sum by 2/1000000 reports the surface area in square metres. "
        "Positive real lengths come from the source; fractional millimetres and every edge permutation remain allowed.",
        goal=False)
    cavity_units["model"]["decision"] = "optimization"
    cavity_units["model"]["objectives"] = [{
        "sense": "minimize", "expr": {"var": "surface_area_m2"},
        "span": cavity_units["model"]["constraints"].pop()["span"],
    }]
    cavity_units["required_outputs"] = [
        {"name": "edges_mm", "sort": "Real", "shape": [3]},
        {"name": "surface_area_m2", "sort": "Real", "shape": []},
    ]
    return {
        "linear_money_unit_conversion": money_units,
        "product_and_area_unit_conversion": cavity_units,
        "shared_identity_coordinates": shared_ids,
        "distinct_label_objective": distinct_labels,
        "percentage_of_combined_total": example(
            ["Let resin and filler be nonnegative real masses in grams.",
             "Resin makes up at least 37 percent of their combined mass."],
            [op("and", op("ge", resin, zero), op("ge", filler, zero)),
             op("ge", resin, op("mul", {"literal": "37/100", "sort": "Real"},
                                op("add", resin, filler)))],
            [{"name": name, "sort": "Real"} for name in ("resin", "filler")], [],
            "The combined total is resin + filler. This is equivalently 63*resin >= 37*filler. "
            "Zero total remains allowed; the source does not require a positive mass.", goal=False),
        "exact_fraction_of_quantity": example(
            ["Let load be a nonnegative real mass in grams.",
             "Reserve exactly one seventh of load as a real mass named reserve."],
            [op("ge", load, zero),
             op("eq", reserve, op("mul", {"literal": "1/7", "sort": "Real"}, load))],
            [{"name": name, "sort": "Real"} for name in ("load", "reserve")], [],
            "The fraction is exact. A finite decimal approximation would change the feasible relation.",
            goal=False),
        "shared_numeric_attribute": example(
            ["Rho has a temperature below 5 degrees.",
             "Conclusion: Rho has a temperature above 5 degrees."],
            [op("lt", temperature, threshold),
             op("eq", {"var": "somt_goal"}, op("gt", temperature, threshold))],
            [{"name": "rho", "sort": entity}],
            [{"name": "temperature", "arguments": [entity], "result": "Real"}],
            "Both comparisons use the same Real-valued function and unit. No extra numeric bounds are assumed."),
        "universal_without_existence": example(
            ["All gliders are light.", "Conclusion: At least one glider exists."],
            [rule, op("eq", {"var": "somt_goal"}, quantify("exists", apply("glider", "x")))],
            [], predicates,
            "The Entity sort is nonempty, but the glider predicate may have no members."),
        "explicit_category_membership": example(
            ["All gliders are light.", "Neri is a glider.", "Conclusion: Neri is light."],
            [rule, apply("glider", "neri"),
             op("eq", {"var": "somt_goal"}, apply("light", "neri"))],
            [{"name": "neri", "sort": entity}], predicates,
            "The named individual satisfies the rule's guard because membership is explicitly stated."),
    }
