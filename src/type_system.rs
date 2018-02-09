use expressions::*;

pub fn type_check(ctx: &mut Vec<Expression>, expr: &Expression)
    -> Result<Expression, ()>
{
    use expressions::Expression::*;
    match *expr {
        Variable(i) => {
            Ok(ctx[ctx.len() - i].clone())
        },

        IntroPoint => {
            Ok(unit())
        },

        IntroTT | IntroFF => {
            Ok(bool())
        },
        ElimIf {
            ref condition,
            ref tt_branch,
            ref ff_branch,
            ref out_type,
        } => {
            let condition_type_expr = type_check(ctx, condition)?;
            let condition_type = condition_type_expr.reduce();
            if condition_type == bool() {
                let tt_check = type_check(ctx, tt_branch)?;
                let tt_check = tt_check.reduce();

                let ff_check = type_check(ctx, ff_branch)?;
                let ff_check = ff_check.reduce();

                let tt_expected = out_type.substitute(&tt());
                let tt_expected = tt_expected.reduce();

                let ff_expected = out_type.substitute(&ff());
                let ff_expected = ff_expected.reduce();

                if tt_check == tt_expected && ff_check == ff_expected {
                    let out_type = out_type.substitute(condition);
                    Ok(out_type)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type_clone = (**in_type).clone();
            ctx.push(in_type_clone);
            let maybe_codomain = type_check(ctx, body);
            let domain = ctx.pop().unwrap();
            let codomain = maybe_codomain?;
            Ok(pi(domain, codomain))
        },
        ElimApplication { ref function, ref argument } => {
            let fun_type = type_check(ctx, function)?;
            let fun_type = fun_type.reduce();
            let arg_type = type_check(ctx, argument)?;
            if let Expression::IntroType(maybe_pi) = fun_type {
                let maybe_pi = *maybe_pi;
                if let Type::Pi { domain, codomain } = maybe_pi {
                    if arg_type == *domain {
                        let codomain = codomain.substitute(&argument);
                        Ok(codomain)
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            let fst_type = type_check(ctx, fst)?;
            let inner_snd_type = type_check(ctx, snd)?;
            let inner_snd_type = inner_snd_type.reduce();
            let expected_snd_type = snd_type.substitute(fst);
            let expected_snd_type = expected_snd_type.reduce();
            if inner_snd_type == expected_snd_type {
                Ok(sigma(fst_type, (**snd_type).clone()))
            } else {
                Err(())
            }
        },
        ElimFst { ref pair } => {
            let pair_type = type_check(ctx, pair)?;
            let pair_type = pair_type.reduce();
            // TODO write functions to do this type evaluation + checking
            if let Expression::IntroType(maybe_sigma) = pair_type {
                if let Type::Sigma { fst_type, .. } = *maybe_sigma {
                    Ok(*fst_type)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },
        ElimSnd { ref pair } => {
            let pair_type = type_check(ctx, pair)?;
            let pair_type = pair_type.reduce();
            if let Expression::IntroType(maybe_sigma) = pair_type {
                if let Type::Sigma { snd_type, .. } = *maybe_sigma {
                    let pair = pair.clone();
                    let fst = ElimFst { pair };
                    let snd_type = snd_type.substitute(&fst);
                    Ok(snd_type)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroType(_) => {
            // TODO check types properly :P
            Ok(universe())
        },
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! type_checks {
        ($before: expr => $after: expr) => {{
            let mut ctx = Vec::new();
            let before = $before;
            let after = type_check(&mut ctx, &before);
            assert_eq!(Ok($after), after);
            // mainly for `variable_management` but should always pass
            assert_eq!(*ctx, []);
        }}
    }

    macro_rules! type_error {
        ($expr: expr) => {{
            let mut ctx = Vec::new();
            let expr = $expr;
            let err = type_check(&mut ctx, &expr);
            assert_eq!(Err(()), err);
            assert_eq!(*ctx, []);
        }}
    }

    #[test]
    fn discrete_type_checking() {
        type_checks!(point() => unit());

        type_checks!(tt() => bool());

        type_checks!(ff() => bool());

        type_checks!(if_then_else(tt(), point(), point(), unit()) => unit());

        type_error!(if_then_else(point(), tt(), tt(), bool()));

        type_error!(if_then_else(tt(), tt(), point(), bool()));
    }

    #[test]
    fn function_type_checking() {
        type_checks!(lambda(unit(), var(1)) => pi(unit(), unit()));

        type_checks!(apply(lambda(bool(), point()), tt()) => unit());

        type_error!(apply(lambda(bool(), point()), point()));

        type_error!(apply(point(), tt()));
    }

    #[test]
    fn pair_type_checking() {
        type_checks!(pair(point(), tt(), bool()) => sigma(unit(), bool()));

        type_checks!(fst(pair(point(), tt(), bool())) => unit());

        type_checks!(snd(pair(point(), tt(), bool())) => bool());

        type_error!(fst(point()));

        type_error!(snd(point()));
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &Expression::IntroPoint);
        assert_eq!(*ctx, []);

        type_checks!(
            // \x: Unit -> \y: Bool -> <y, x>
            lambda(unit(), lambda(bool(), pair(var(1), var(2), unit())))
        =>
            // Unit -> Bool -> Bool * Unit
            pi(unit(), pi(bool(), sigma(bool(), unit())))
        );
    }

    #[test]
    fn annotation_checks() {
        // `()` is not a type
        type_error!(pair(point(), point(), point()));

        type_error!(lambda(point(), point()));

        type_error!(pair(point(), point(), point()));
    }

    #[test]
    fn dependent_types() {
        // this type family is useful
        let tf = || if_then_else(var(1), bool(), unit(), universe());

        type_checks!(
            lambda(
                bool(),
                apply(
                    lambda(
                        unit(),
                        if_then_else(
                            // if y then tt else ()
                            //   as (if y0 then bool else unit)
                            var(2), tt(), point(), tf()
                        ),
                    ),
                    point()
                )
            )
        =>
            // if y then bool else unit
            pi(bool(), tf())
        );

        type_checks!(
            // \x: Bool -> \y: (if x then Bool else Unit) -> <x, y>
            lambda(bool(), lambda(tf(), pair(var(2), var(1), tf())))
        =>
            pi(bool(), pi(tf(), sigma(bool(), tf())))
        );

        type_checks!(
            // \A: U -> \B: U -> \x: A -> <tt, x>
            //   as (if t0 then A else B)
            lambda(
                universe(),
                lambda(
                    universe(),
                    lambda(
                        var(2),
                        pair(
                            tt(), var(2),
                            if_then_else(var(1), var(4), var(3), universe())
                        )
                    )
                )
            )
        =>
            // forall A: U, forall B: U,
            //   A -> Sigma t: Bool, if t then A else U
            pi(universe(), pi(universe(),
                pi(
                    var(2), sigma(bool(),
                    if_then_else(var(1), var(4), var(3), universe()))
                )
            ))
        )
    }
}

