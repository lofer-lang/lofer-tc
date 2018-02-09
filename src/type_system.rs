// TODO turn these into methods on Expression
use eval::{reduce, substitute};  // lovely coupling

#[derive(Clone, PartialEq, Debug)]
pub enum Expression {
    Variable(usize), // variables should be indexed from the end of the list?

    IntroPoint,

    IntroTT,
    IntroFF,
    ElimIf {
        condition: Box<Expression>,
        tt_branch: Box<Expression>,
        ff_branch: Box<Expression>,
        out_type: Box<Expression>,
    },

    IntroLambda {
        in_type: Box<Expression>,
        body: Box<Expression>,
    },
    ElimApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    IntroPair {
        fst: Box<Expression>,
        snd: Box<Expression>,
        snd_type: Box<Expression>,
    },
    ElimFst {
        pair: Box<Expression>,
    },
    ElimSnd {
        pair: Box<Expression>,
    },

    IntroType(Box<Type>),
    // type eliminator one day :o
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Void,
    Unit,
    Bool,
    Pi {
        domain: Box<Expression>,
        codomain: Box<Expression>,
    },
    Sigma {
        fst_type: Box<Expression>,
        snd_type: Box<Expression>,
    },
    Universe/*(usize)*/,
}

pub mod expressions {
    use super::Expression;
    use super::Type;

    pub fn var(n: usize) -> Expression {
        Expression::Variable(n)
    }

    pub fn point() -> Expression {
        Expression::IntroPoint
    }

    pub fn tt() -> Expression {
        Expression::IntroTT
    }

    pub fn ff() -> Expression {
        Expression::IntroFF
    }

    // would make a version with inference, but passing the context in is less
    // intuitive than passing the actual type in
    pub fn if_then_else(
        condition: Expression,
        tt_branch: Expression,
        ff_branch: Expression,
        out_type: Expression,
    ) -> Expression {
        let condition = Box::new(condition);
        let tt_branch = Box::new(tt_branch);
        let ff_branch = Box::new(ff_branch);
        let out_type = Box::new(out_type);
        Expression::ElimIf { condition, tt_branch, ff_branch, out_type }
    }

    pub fn lambda(in_type: Expression, body: Expression)
        -> Expression
    {
        let in_type = Box::new(in_type);
        let body = Box::new(body);
        Expression::IntroLambda { in_type, body }
    }

    pub fn apply(function: Expression, argument: Expression) -> Expression {
        let function = Box::new(function);
        let argument = Box::new(argument);
        Expression::ElimApplication { function, argument }
    }

    // see if-then-else on the subject of type inference
    pub fn pair(fst: Expression, snd: Expression, snd_type: Expression) -> Expression {
        let fst = Box::new(fst);
        let snd = Box::new(snd);
        let snd_type = Box::new(snd_type);
        Expression::IntroPair { fst, snd, snd_type }
    }

    pub fn fst(pair: Expression) -> Expression {
        let pair = Box::new(pair);
        Expression::ElimFst { pair }
    }

    pub fn snd(pair: Expression) -> Expression {
        let pair = Box::new(pair);
        Expression::ElimSnd { pair }
    }

    pub fn simple_type(typ: Type) -> Expression {
        let typ = Box::new(typ);
        Expression::IntroType(typ)
    }

    pub fn void() -> Expression {
        simple_type(Type::Void)
    }

    pub fn unit() -> Expression {
        simple_type(Type::Unit)
    }

    pub fn bool() -> Expression {
        simple_type(Type::Bool)
    }

    pub fn pi(domain: Expression, codomain: Expression) -> Expression {
        let domain = Box::new(domain);
        let codomain = Box::new(codomain);
        let out = Type::Pi { domain, codomain };
        simple_type(out)
    }

    pub fn sigma(fst_type: Expression, snd_type: Expression) -> Expression {
        let fst_type = Box::new(fst_type);
        let snd_type = Box::new(snd_type);
        let out = Type::Sigma { fst_type, snd_type };
        simple_type(out)
    }

    pub fn universe() -> Expression {
        simple_type(Type::Universe)
    }
}

pub fn type_check(ctx: &mut Vec<Expression>, expr: &Expression)
    -> Result<Expression, ()>
{
    use self::Expression::*;
    use self::expressions::*;
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
            let condition_type = reduce(&condition_type_expr);
            if condition_type == bool() {
                let tt_check = type_check(ctx, tt_branch)?;
                let tt_check = reduce(&tt_check);

                let ff_check = type_check(ctx, ff_branch)?;
                let ff_check = reduce(&ff_check);

                let tt_expected = substitute(&out_type, 1, &tt(), true);
                let tt_expected = reduce(&tt_expected);

                let ff_expected = substitute(&out_type, 1, &ff(), true);
                let ff_expected = reduce(&ff_expected);

                if tt_check == tt_expected && ff_check == ff_expected {
                    let out_type = substitute(&out_type, 1, condition, true);
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
            let fun_type = reduce(&fun_type);
            let arg_type = type_check(ctx, argument)?;
            if let Expression::IntroType(maybe_pi) = fun_type {
                let maybe_pi = *maybe_pi;
                if let Type::Pi { domain, codomain } = maybe_pi {
                    if arg_type == *domain {
                        let codomain =
                            substitute(&codomain, 1, &argument, true);
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
            ctx.push(fst_type);
            let maybe_snd_type = type_check(ctx, snd);
            let fst_type = ctx.pop().unwrap();
            let inner_snd_type = maybe_snd_type?;
            let inner_snd_type = reduce(&inner_snd_type);
            let expected_snd_type = substitute(snd_type, 1, fst, true);
            let expected_snd_type = reduce(&expected_snd_type);
            if inner_snd_type == expected_snd_type {
                Ok(sigma(fst_type, (**snd_type).clone()))
            } else {
                Err(())
            }
        },
        ElimFst { ref pair } => {
            let pair_type = type_check(ctx, pair)?;
            let pair_type = reduce(&pair_type);
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
            let pair_type = reduce(&pair_type);
            if let Expression::IntroType(maybe_sigma) = pair_type {
                if let Type::Sigma { snd_type, .. } = *maybe_sigma {
                    let pair = pair.clone();
                    let fst = ElimFst { pair };
                    let snd_type = substitute(&snd_type, 1, &fst, true);
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
    use super::expressions::*;

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

    // passes since sigma will be dependent in the future
    #[test]
    fn strange_diagonal() {
        // unusual to represent this way, but equivalent to <tt, tt>
        type_checks!(pair(tt(), var(1), bool()) => sigma(bool(), bool()));
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &Expression::IntroPoint);
        assert_eq!(*ctx, []);

        type_checks!(
            // \x: Unit -> \y: Bool -> <y, x>
            lambda(unit(), lambda(bool(), pair(var(1), var(3), unit())))
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
        type_checks!(
            lambda(
                bool(),
                apply(
                    lambda(
                        unit(),
                        if_then_else(
                            // if y then tt else ()
                            //   as (if y0 then bool else unit)
                            var(2), tt(), point(),
                            if_then_else(var(1), bool(), unit(), universe())
                        ),
                    ),
                    point()
                )
            )
        =>
            // if y then bool else unit
            pi(bool(), if_then_else(var(1), bool(), unit(), universe()))
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

