use super::*;

fn eval_on(globals: &Vec<Item>, xs: &mut Vec<Expr>, ctx_size: &mut usize, incr: bool) {
    for x in xs {
        eval(globals, x, *ctx_size);
        if incr {
            *ctx_size += 1;
        }
    }
}

pub(super) fn eval(globals: &Vec<Item>, expr: &mut Expr, mut ctx_size: usize) {
    eval_on(globals, &mut expr.arrow_params, &mut ctx_size, true);
    eval_on(globals, &mut expr.tail, &mut ctx_size, false);

    while let Ident::Global(i) = expr.head {
        if globals[i].def.is_none() {
            break;
        }
        let &(param_num, ref def) = globals[i].def.as_ref().unwrap();
        if expr.tail.len() < param_num {
            break;
        }

        let mut result = subst(
            &def, 0, 0,
            &expr.tail[0..param_num], ctx_size,
        );
        // recurse... often redundant... @Performance? combine with subst?
        // type checking should prevent associativity problems
        // A -> (B -> x y z) w
        eval_on(globals, &mut result.arrow_params, &mut ctx_size, true);
        eval_on(globals, &mut result.tail, &mut ctx_size, false);
        // @Performance we are allocating again every time...
        // could just combine these steps or something more tricky
        expr.tail.drain(0..param_num);
        expr.insert(result);
    }
}

// takes an expression M valid in G1, (s + m + e variables)
// and a set of arguments X1..Xm valid in G2 (n variables) where s <= n
// then generates an expression M[x(s+i) <- Xi, x(s+m+i) <- x(n+i)]
// but with Xi[x(n+i) <- x(n+e+i)] in each substitution,
// in cases where arrow expressions are substituted _into_ arrow expressions
pub(super) fn subst(
    base: &Expr, shared_ctx_size: usize, mut extra_ctx_size: usize,
    args: &[Expr], arg_ctx_size: usize,
) -> Expr {
    // just a dumb default... we overwrite everything
    let mut result = Expr::ident(Ident::Universe(0));
    result.arrow_params = Vec::with_capacity(base.arrow_params.len());
    for ex in &base.arrow_params {
        result.arrow_params.push(
             subst(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
        extra_ctx_size += 1;
    }
    result.tail = Vec::with_capacity(base.tail.len());
    for ex in &base.tail {
        result.tail.push(
             subst(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
    }
    match base.head {
        Ident::Local(i) => {
            if i < shared_ctx_size {
                result.head =  Ident::Local(i);
            } else if i - shared_ctx_size < args.len() {
                let arg = deepen(
                    &args[i - shared_ctx_size],
                    arg_ctx_size,
                    extra_ctx_size,
                );
                result.insert(arg);
            } else {
                let e = i - (shared_ctx_size + args.len());
                result.head = Ident::Local(arg_ctx_size + e);
            }
        },
        _ => result.head = base.head,
    }
    result
}

pub(super) fn subst_metas(
    base: &Expr, shared_ctx_size: usize, mut extra_ctx_size: usize,
    args: &[unify::MetaSolution], arg_ctx_size: usize,
) -> Expr {
    // just a dumb default... we overwrite everything
    let mut result = Expr::ident(Ident::Universe(0));
    result.arrow_params = Vec::with_capacity(base.arrow_params.len());
    for ex in &base.arrow_params {
        result.arrow_params.push(
             subst_metas(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
        extra_ctx_size += 1;
    }
    result.tail = Vec::with_capacity(base.tail.len());
    for ex in &base.tail {
        result.tail.push(
             subst_metas(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
    }
    match base.head {
        Ident::Meta(i, n) => {
            let sol = &args[i];
            if n >= 2 {
                result.head = Ident::Universe(sol.level + n - 2);
            } else {
                let arg = if n == 0 { &sol.val } else { &sol.ty };
                let arg = deepen(
                    arg,
                    arg_ctx_size,
                    extra_ctx_size,
                );
                result.insert(arg);
            }
        },
        _ => result.head = base.head,
    }
    result
}

fn deepen(arg: &Expr, arg_ctx_size: usize, extra: usize) -> Expr {
    let mut arrow_params = Vec::with_capacity(arg.arrow_params.len());
    for ex in &arg.arrow_params {
        arrow_params.push(
            deepen(ex, arg_ctx_size, extra)
        );
    }
    let mut tail = Vec::with_capacity(arg.tail.len());
    for ex in &arg.tail {
        tail.push(
            deepen(ex, arg_ctx_size, extra)
        );
    }
    let mut head = arg.head;
    if let Ident::Local(i) = &mut head {
        if *i >= arg_ctx_size {
            *i += extra;
        }
    }
    Expr { arrow_params, head, tail }
}

