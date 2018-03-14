use std::collections::VecDeque;

use programs::*;

fn get_args(mut expr: Expression, mut args: VecDeque<Expression>)
    -> (Expression, VecDeque<Expression>)
{
    use programs::Expression::*;
    while let ElimApplication { function, argument } = expr {
        expr = *function;
        args.push_front(*argument);
    }

    (expr, args)
}

// do we recurse one comparison or both?
fn recurse_reduction_check(
    self_fun: &Expression,
    self_args: &VecDeque<Expression>,
    other_fun: &Expression,
    other_args: &VecDeque<Expression>,
) -> bool {
    if self_args.len() != other_args.len() {
        return false;
    }
    if !self_fun.clone().reduces_to(other_fun.clone()) {
        return false;
    }
    for i in 0..self_args.len() {
        if !self_args[i].clone().reduces_to(other_args[i].clone()) {
            return false;
        }
    }
    true
}

impl Expression {
    // reduces to WHNF
    pub fn reduce_weak(self: Expression) -> Expression {
        let (fun, args) = reduce_args(self);
        reapply_args(fun, args)
    }

    // further reduces data, but not functions
    pub fn reduce(self: Expression) -> Expression {
        let (fun, mut args) = reduce_args(self);
        if fun == Expression::IntroPair {
            args = args
                .into_iter()
                .map(Expression::reduce)
                .collect();
        /*
        } else if let Expression::IntroLambda { body } = fun {
            // return because args must be empty anyway
            return lambda(body.reduce());
        */
        }
        reapply_args(fun, args)
    }

    pub fn reduces_to(mut self: Self, other: Self) -> bool {
        if self == other {
            return true;
        }

        let (other, other_args) = get_args(other, VecDeque::new());
        let mut self_args = VecDeque::new();

        loop {
            if recurse_reduction_check(
                &self,
                &self_args,
                &other,
                &other_args,
            ) {
                return true;
            }

            let (new_fun, new_args, did_reduction) =
                reduce_args_once(self, self_args);
            self = new_fun;
            self_args = new_args;

            if !did_reduction {
                return false;
            }
        }
    }

}

fn reapply_args(mut fun: Expression, args: VecDeque<Expression>)
    -> Expression
{
    for arg in args {
        fun = apply(fun, arg);
    }
    fun
}

fn reduce_args(mut fun: Expression)
    -> (Expression, VecDeque<Expression>)
{
    let mut args = VecDeque::new();
    loop {
        let (new_fun, new_args, did_reduction) = reduce_args_once(fun, args);
        if !did_reduction {
            return (new_fun, new_args);
        }
        fun = new_fun;
        args = new_args;
    }
}

fn reduce_weak_once(expr: Expression) -> (Expression, bool) {
    let (fun, args) = get_args(expr, VecDeque::new());
    let (fun, args, did_reduce) = reduce_args_once(fun, args);
    let expr = reapply_args(fun, args);
    (expr, did_reduce)
}

fn reduce_args_once(fun: Expression, mut args: VecDeque<Expression>)
    -> (Expression, VecDeque<Expression>, bool)
{
    use programs::Expression::*;
    match fun {
        ElimApplication { .. } => {
            let (fun, args) = get_args(fun, args);
            return (fun, args, true);
        },
        IntroLambda { .. } => {
            if let Some(arg) = args.pop_front() {
                if let IntroLambda { body } = fun {
                    let new_expr = body.substitute(&arg);
                    return (new_expr, args, true);
                } else {
                    unreachable!();
                }
            }
        },
        ElimIf => {
            if args.len() >= 3 {
                let tt_branch = args.pop_front().unwrap();
                let ff_branch = args.pop_front().unwrap();
                let condition = args.pop_front().unwrap();

                // we could do reduce_args_once to search more thoroughly
                // during type checking
                let (condition, did_reduce) = reduce_weak_once(condition);
                if !did_reduce {
                    if condition == IntroTT {
                        return (tt_branch, args, true)
                    } else if condition == IntroFF {
                        return (ff_branch, args, true)
                    }
                }
                // condition not fully normalized, move on
                args.push_front(condition);
                args.push_front(ff_branch);
                args.push_front(tt_branch);
                return (fun, args, did_reduce);
            }
        },
        ElimUncurry => {
            if args.len() >= 2 {
                let function = args.pop_front().unwrap();
                let pair = args.pop_front().unwrap();

                let (mut pair, did_reduce) = reduce_weak_once(pair);
                if !did_reduce {
                    let (rule, mut terms) = get_args(pair, VecDeque::new());
                    if rule == IntroPair && terms.len() == 2 {
                        // reduces `uncurry f (Pair x y) z...`
                        // into `f x y z...`
                        terms.append(&mut args);
                        return (function, terms, true);
                    }

                    //else
                    pair = reapply_args(rule, terms);
                }
                args.push_front(pair);
                args.push_front(function);
                return (fun, args, did_reduce);
            }
        },

        _ => (),
    }
    (fun, args, false)
}

#[cfg(test)]
mod tests {
    use programs::*;

    macro_rules! irreducible {
        ($before: expr) => {{
            let before = $before;
            let after = before.clone().reduce();
            assert_eq!(before, after);
        }}
    }

    macro_rules! reduces {
        ($before: expr => $after: expr) => {{
            let before = $before;
            let after = before.reduce();
            assert_eq!(after, $after);
        }}
    }

    #[test]
    fn irreducible_intros() {
        irreducible!(point());
        irreducible!(tt());
        irreducible!(ff());
        irreducible!(lambda(point()));
        irreducible!(pair(tt(), ff()));
    }

    #[test]
    fn reduce_bool() {
        reduces!(if_then_else(tt(), tt(), ff()) => tt());

        reduces!(if_then_else(ff(), tt(), ff()) => ff());

        irreducible!(if_then_else(var(1), tt(), ff()));
    }

    #[test]
    fn reduce_lambda() {
        reduces!(apply(lambda(var(0)), tt()) => tt());

        reduces!(
            // (\x: Bool -> if x then ff else tt) tt
            apply(
                lambda(
                    if_then_else(var(0), ff(), tt()),
                ),
                tt(),
            )
        =>
            ff()
        );

        irreducible!(apply(var(1), point()));
    }

    #[test]
    fn reduce_pair() {
        reduces!(fst(pair(tt(), ff())) => tt());
        reduces!(snd(pair(tt(), ff())) => ff());

        irreducible!(fst(var(1)));
        irreducible!(snd(var(1)));
    }

    #[test]
    fn branches_block_recursion() {
        // not allowed in Agda or Coq
        // freeze = fix (\freeze: Void -> freeze)
        let freeze = || fix(lambda(var(0)));

        // recursive things don't reduce until a branch is chosen
        irreducible!(if_then_else(var(0), freeze(), freeze()));

        let term = ||
            fix(lambda(if_then_else(var(1), var(0), tt())));

        reduces!(
            term()
        =>
            if_then_else(var(0), term(), tt())
        );

        // currently reduce() doesn't head normalize, it may never.
        irreducible!(lambda(apply(lambda(var(0)), point())));

        // term: Bool -> Bool
        // term = fix (\f: Bool -> Bool. \x: Bool. f x)
        let term = ||
            fix(
                lambda(lambda(apply(var(1), var(0)))
                )
            );
        reduces!(
            term()
        =>
            lambda(apply(term(), var(0)))
        );
    }

    #[test]
    fn peano() {
        // these should be in a module somewhere since multiple tests could
        // use them
        /*
        let sum = || lambda(universe(), lambda(universe(),
            sigma(bool(), if_then_else(var(0), var(2), var(1), universe()))
        ));
        let apply_sum = |a, b| apply(apply(sum(), a), b);
        reduces!(
            apply_sum(bool(), unit())
        =>
            sigma(bool(), if_then_else(var(0), bool(), unit(), universe()))
        );

        let nat = || fix(lambda(universe(), apply_sum(var(0), unit())));
        */

        let zero = || pair(ff(), point());
        let succ = || lambda(pair(tt(), var(0)));
        let apply_succ = |x| apply(succ(), x);

        /* nope nope nope
        let nat_elim = ||
            lambda(pi(nat(), universe()),
            lambda(apply(var(0), zero()),
            lambda(
                pi(nat(),
                pi(apply(var(2), var(0)),
                    apply(var(3), apply(succ(), var(1)))
                )),
            fix(lambda(pi(nat(), apply(var(), var(0))),
                lambda(nat(), if_then_else(fst(var(0)), base, apply(ind, apply(self, snd(var(0)))), apply(prop, var(1)))))))))
                */

        // this probably won't type check as is
        let plus = ||
            lambda(fix(lambda(lambda(
                if_then_else(
                    fst(var(0)),
                        apply(succ(),
                        apply(var(1),
                        snd(var(0)))),
                    var(2),
                )
            ))));

        let two = || apply_succ(apply_succ(zero()));
        let four = || apply_succ(apply_succ(two())).reduce_weak();

        reduces!(apply(apply(plus(), two()), two()) => four());
    }

    #[test]
    fn other_recursive_things() {
        unimplemented!();
    }
}

