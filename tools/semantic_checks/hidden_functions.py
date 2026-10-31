"""Close private total functions using one nested array witness per declaration.

Applications, ``as-array`` and ``map`` share that witness. Declaration
parameters are inspected as well as expression children: an unsupported
operator embedding a private function must fail before an equivalence verdict.
The caller existentially hides the returned arrays with other private values.

This uses Z3's array/function-space interpretation:
https://microsoft.github.io/z3guide/docs/theories/Arrays/#beyond-arrays
The visible interface consists of values, not function declarations.
"""


def encode_hidden_functions(body):
    import z3

    private = {}
    dependencies = {}
    inspecting = set()

    def annotation_terms(node):
        terms = [node.body()]
        for index in range(node.num_patterns()):
            terms.extend(node.pattern(index).children())
        terms.extend(node.no_pattern(i) for i in range(node.num_no_patterns()))
        return terms

    def inspect_expression(expression):
        found = set()
        pending, visited = [expression], set()
        while pending:
            node = pending.pop()
            if node.get_id() in visited:
                continue
            visited.add(node.get_id())
            if z3.is_quantifier(node):
                pending.extend(annotation_terms(node))
            elif z3.is_app(node):
                found.update(inspect_declaration(node.decl()))
                pending.extend(node.children())
        return found

    def inspect_declaration(declaration):
        key = declaration.get_id()
        if key in dependencies:
            return dependencies[key]
        if key in inspecting:
            return set()
        # Recursive definitions live in Z3's plugin, not in expression children
        # or declaration parameters. Their private dependencies cannot be
        # audited through this API; silently retaining them would be unsound.
        if declaration.kind() == z3.Z3_OP_RECURSIVE:
            raise ValueError('hidden-function projection requires explicit expansion '
                             'of recursive function definitions: ' + str(declaration.name()))
        inspecting.add(key)
        found = set()
        if declaration.kind() == z3.Z3_OP_UNINTERPRETED and declaration.arity():
            private[key] = declaration
            found.add(key)
        for parameter in declaration.params():
            # Z3 versions expose declaration-valued AST parameters either as
            # FuncDeclRef or generic ExprRef. Inspect the actual AST kind.
            if not isinstance(parameter, z3.AstRef):
                continue
            kind = z3.Z3_get_ast_kind(parameter.ctx_ref(), parameter.as_ast())
            if kind == z3.Z3_FUNC_DECL_AST:
                embedded = z3.FuncDeclRef(z3.Z3_to_func_decl(
                    parameter.ctx_ref(), parameter.as_ast()), parameter.ctx)
                found.update(inspect_declaration(embedded))
            elif kind in (z3.Z3_APP_AST, z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST):
                found.update(inspect_expression(z3.z3._to_expr_ref(
                    parameter.as_ast(), parameter.ctx)))
        if found and declaration.kind() not in (
                z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_AS_ARRAY, z3.Z3_OP_ARRAY_MAP):
            raise ValueError('hidden-function projection does not support embedded '
                             'private functions in operator ' + str(declaration.name()))
        dependencies[key] = found
        inspecting.remove(key)
        return found

    inspect_expression(body)
    if not private:
        return body, ()
    witnesses = {}
    for key, declaration in private.items():
        sort = declaration.range()
        for index in reversed(range(declaration.arity())):
            sort = z3.ArraySort(declaration.domain(index), sort)
        witnesses[key] = z3.FreshConst(sort, 'hidden_function')

    def application(declaration, arguments):
        args = (z3.Ast * len(arguments))(*[arg.as_ast() for arg in arguments])
        return z3.z3._to_expr_ref(z3.Z3_mk_app(
            declaration.ctx_ref(), declaration.ast, len(arguments), args), declaration.ctx)

    def apply(declaration, arguments):
        key = declaration.get_id()
        if key in witnesses:
            value = witnesses[key]
            for argument in arguments:
                value = z3.Select(value, argument)
            return value
        if not dependencies.get(key):
            return application(declaration, arguments)
        if declaration.kind() == z3.Z3_OP_AS_ARRAY:
            function = z3.get_as_array_func(declaration())
            if function.arity() == 1 and function.get_id() in witnesses:
                # The unary witness already has exactly the as-array sort,
                # including an array-valued range. An eta-expanding Lambda
                # would hide finite reads behind an unnecessary binder.
                return witnesses[function.get_id()]
            indices = [z3.FreshConst(function.domain(i), 'function_index')
                       for i in range(function.arity())]
            # A multi-domain array is not a nested array. Lambda restores the
            # original array sort while selecting the shared nested witness.
            return z3.Lambda(indices, apply(function, indices))
        if declaration.kind() == z3.Z3_OP_ARRAY_MAP:
            placeholders = [z3.FreshConst(declaration.domain(i), 'map_argument')
                            for i in range(declaration.arity())]
            function = z3.get_map_func(declaration(*placeholders))
            sort = declaration.range()
            arity = z3.Z3_get_array_arity(sort.ctx_ref(), sort.ast)
            indices = [z3.FreshConst(sort.domain_n(i), 'map_index') for i in range(arity)]
            value = apply(function, [z3.Select(array, *indices) for array in placeholders])
            template = z3.Lambda(indices, value)
            # Capture-avoiding substitution shifts bound variables in actual
            # arguments below the new lambda, including nested map lambdas.
            return z3.substitute(template, *zip(placeholders, arguments))
        raise AssertionError('unchecked embedded function operator')

    def rebuild_quantifier(node, values):
        count = node.num_vars()
        sorts = (z3.Sort * count)(*[node.var_sort(i).ast for i in range(count)])
        names = (z3.Symbol * count)(*[z3.Z3_get_quantifier_bound_name(
            node.ctx_ref(), node.ast, i) for i in range(count)])
        if node.is_lambda():
            ast = z3.Z3_mk_lambda(node.ctx_ref(), count, sorts, names, values[0].as_ast())
        else:
            offset, patterns = 1, []
            for index in range(node.num_patterns()):
                width = node.pattern(index).num_args()
                patterns.append(z3.MultiPattern(*values[offset:offset + width]))
                offset += width
            pats = (z3.Pattern * len(patterns))(*[p.ast for p in patterns])
            no_pats = (z3.Ast * (len(values) - offset))(*[p.as_ast() for p in values[offset:]])
            ast = z3.Z3_mk_quantifier_ex(
                node.ctx_ref(), node.is_forall(), node.weight(),
                z3.Z3_get_quantifier_id(node.ctx_ref(), node.ast),
                z3.Z3_get_quantifier_skolem_id(node.ctx_ref(), node.ast),
                len(patterns), pats, len(no_pats), no_pats, count, sorts, names,
                values[0].as_ast())
        return z3.QuantifierRef(ast, node.ctx)

    # Iterative traversal avoids Python recursion on large formulas. Retain
    # de Bruijn indices, binder names and transformed trigger annotations.
    cache, pending = {}, [(body, False)]
    while pending:
        node, ready = pending.pop()
        key = node.get_id()
        if key in cache:
            continue
        children = (annotation_terms(node) if z3.is_quantifier(node)
                    else node.children() if z3.is_app(node) else [])
        if not ready and children:
            pending.append((node, True))
            pending.extend((child, False) for child in children if child.get_id() not in cache)
            continue
        values = [cache[child.get_id()] for child in children]
        if z3.is_quantifier(node):
            cache[key] = rebuild_quantifier(node, values)
        elif z3.is_app(node):
            cache[key] = apply(node.decl(), values)
        else:
            cache[key] = node
    return cache[body.get_id()], tuple(witnesses.values())
