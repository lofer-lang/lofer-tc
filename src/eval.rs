use std::collections::VecDeque;

use programs::*;

fn get_args(expr: &Expression) -> (&Expression, Vec<&Expression>) {
    let (fun, mut args) = get_args_helper(expr, Vec::new());
    args.reverse();
    (fun, args)
}

fn get_args_helper<'a>(expr: &'a Expression, mut args: Vec<&'a Expression>)
    -> (&'a Expression, Vec<&'a Expression>)
{
    use programs::Expression::*;
    if let ElimApplication { ref function, ref argument } = *expr {
        args.push(argument);
        get_args_helper(function, args)
    } else {
        (expr, args)
    }
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
        use programs::Expression::*;
        match fun {
            ElimApplication { function, argument } => {
                fun = *function;
                args.push_front(*argument);
            },
            IntroLambda { body } => {
                if let Some(arg) = args.pop_front() {
                    fun = body.substitute(&arg);
                } else {
                    // back-track
                    fun = IntroLambda { body };
                    break;
                }
            },
            ElimIf => {
                if args.len() >= 3 {
                    let tt_branch = args.pop_front().unwrap();
                    let ff_branch = args.pop_front().unwrap();
                    let condition = args.pop_front().unwrap();

                    let condition = condition.reduce_weak();
                    if condition == IntroTT {
                        fun = tt_branch;
                    } else if condition == IntroFF {
                        fun = ff_branch;
                    } else {
                        // condition can't normalize, move on
                        fun = apply(fun, tt_branch);
                        fun = apply(fun, ff_branch);
                        fun = apply(fun, condition);
                        break;
                    }
                } else {
                    break;
                }
            },
            ElimUncurry => {
                if args.len() >= 2 {
                    let function = args.pop_front().unwrap();
                    let pair = args.pop_front().unwrap();

                    let (rule, mut terms) = reduce_args(pair);
                    if rule == IntroPair && terms.len() == 2 {
                        // reduces `uncurry f (Pair x y) z...`
                        // into `f x y z...`
                        fun = function;

                        terms.append(&mut args);
                        args = terms;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            },

            _ => break,
        }
    }
    (fun, args)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! irreducible {
        ($before: expr) => {{
            let before = $before;
            let after = reduce(&before, true);
            assert_eq!(before, after);
        }}
    }

    macro_rules! reduces {
        ($before: expr => $after: expr) => {{
            let before = $before;
            let after = reduce(&before, true);
            assert_eq!(after, $after);
        }}
    }

    #[test]
    fn irreducible_intros() {
        irreducible!(point());
        irreducible!(tt());
        irreducible!(ff());
        irreducible!(lambda(unit(), point()));
        irreducible!(pair(tt(), ff(), bool()));
    }

    #[test]
    fn reduce_bool() {
        reduces!(if_then_else(tt(), tt(), ff(), bool()) => tt());

        reduces!(if_then_else(ff(), tt(), ff(), bool()) => ff());

        irreducible!(if_then_else(var(1), tt(), ff(), bool()));
    }

    #[test]
    fn reduce_lambda() {
        reduces!(apply(lambda(bool(), var(0)), tt()) => tt());

        reduces!(
            // (\x: Bool -> if x then ff else tt) tt
            apply(
                lambda(
                    bool(),
                    if_then_else(var(0), ff(), tt(), bool()),
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
        reduces!(fst(pair(tt(), ff(), bool())) => tt());
        reduces!(snd(pair(tt(), ff(), bool())) => ff());

        irreducible!(fst(var(1)));
        irreducible!(snd(var(1)));
    }

    #[test]
    fn branches_block_recursion() {
        // not allowed in Agda or Coq
        // freeze = fix (\freeze: Void -> freeze)
        let freeze = || fix(lambda(void(), var(0)));

        // recursive things don't reduce until a branch is chosen
        irreducible!(if_then_else(var(0), freeze(), freeze(), void()));

        let term = ||
            fix(lambda(bool(), if_then_else(var(1), var(0), tt(), bool())));

        reduces!(
            term()
        =>
            if_then_else(var(0), term(), tt(), bool())
        );

        // not sure if this is necessary but recursive things don't
        // reduce until functions have been applied
        irreducible!(lambda(bool(), freeze()));

        let term = ||
            fix(
                lambda(
                    pi(bool(), bool()),
                    lambda(bool(), apply(var(1), var(0)))
                )
            );
        reduces!(
            term()
        =>
            lambda(bool(), apply(term(), var(0)))
        );
    }

    #[test]
    fn peano() {
        // these should be in a module somewhere since multiple tests could
        // use them
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

        let zero = || pair(ff(), point(), nat());
        let succ = || lambda(nat(), pair(tt(), var(0), nat()));
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
            lambda(nat(),
            fix(lambda(pi(nat(), nat()),
            lambda(nat(),
                if_then_else(
                    fst(var(0)),
                        apply(succ(),
                        apply(var(1),
                        snd(var(0)))),
                    var(2),
                    nat(),
                )
            ))));

        let two = || apply_succ(apply_succ(zero()));
        let four = || apply_succ(apply_succ(two())).reduce_lazy();

        reduces!(apply(apply(plus(), two()), two()) => four());
    }

    #[test]
    fn other_recursive_things() {
        unimplemented!();
    }
}

