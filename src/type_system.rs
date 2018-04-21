use untyped::*;
use typed;
use substitution::deepen;

type Context = Vec<(String, Expression)>;

fn find_var<'a>(ctx: &'a Context, name: &String) -> (usize, &'a Expression) {
    for i in 0..ctx.len() {
        if ctx[ctx.len() - i - 1].0 == *name {
            return (i, &ctx[ctx.len() - i - 1].1);
        }
    }
    panic!("Name not in scope: `{}`", name);
}

pub fn type_check(ctx: &mut Context, expr: &typed::Expression)
    -> Result<Expression, TypeCheckError>
{
    use typed::Expression::*;
    match *expr {
        Variable { ref name } => {
            let (i, typ) = find_var(ctx, name);
            Ok(deepen(typ, i + 1, 0))
        },

        IntroLambda { ref var_name, ref var_type, ref body } => {
            Ok(type_check_lambda(ctx, var_name, var_type, body)?)
        },
        ElimApplication { ref function, ref argument } => {
            Ok(type_check_apply(ctx, function, argument)?)
        },

        ElimAbsurd { ref output_type } => {
            Ok(pi(void(), output_type.convert()))
        },

        IntroPoint => {
            Ok(unit())
        },
        ElimTrivial { ref predicate } => {
            let predicate = predicate.convert();
            let predicate = |x| apply(predicate.clone(), x);
            Ok(pi(predicate(point()), pi(unit(), predicate(var(0)))))
        },

        IntroTT | IntroFF => {
            Ok(bool())
        },
        ElimIf {
            ref out_type,
        } => {
            let out_type = out_type.convert();
            let out_type = |x| apply(out_type.clone(), x);
            Ok(
                pi(out_type(tt()),
                 pi(out_type(ff()),
                  pi(bool(),
                   out_type(var(0)))))
            )
        },

        IntroPair { ref fst_type, ref snd_type } => {
            let fst_type = fst_type.convert();
            let fst_type = || fst_type.clone();
            let snd_type = snd_type.convert();
            let snd_type = || snd_type.clone();
            Ok(
                pi(fst_type(),
                 pi(snd_type(),
                  sigma(fst_type(), snd_type())))
            )
        },
        ElimUncurry { ref fst_type, ref snd_type, ref result_type } => {
            let fst_type = fst_type.convert();
            let fst_type = || fst_type.clone();
            let snd_type = snd_type.convert();
            let snd_type = || snd_type.clone();
            let result_type = result_type.convert();
            let result_type = || result_type.clone();
            Ok(pi(
                pi(fst_type(), pi(snd_type(), result_type())),
                pi(sigma(fst_type(), snd_type()), result_type()),
            ))
        },

        IntroType(_) => {
            // TODO check types properly :P
            Ok(universe())
        },

        SpecialFix { ref output_type } => {
            let output_type = output_type.convert();
            let output_type = || output_type.clone();
            Ok(pi(pi(output_type(), output_type()), output_type()))
        },
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum ErrorPath {
    InFunction,
    InArgument,
}

#[derive(PartialEq, Debug, Clone)]
pub struct TypeCheckError {
    // path is in reverse order
    path: Vec<ErrorPath>,
    expected: Expression,
    actual: Expression,
}

impl TypeCheckError {
    fn with_context(mut self: Self, context: ErrorPath) -> Self {
        self.path.push(context);
        self
    }
}

fn type_check_lambda(
    ctx: &mut Context,
    var_name: &String,
    var_type: &typed::Expression,
    body: &typed::Expression,
) -> Result<Expression, TypeCheckError> {
    ctx.push((var_name.clone(), var_type.convert()));
    let maybe_codomain = type_check(ctx, body);
    let domain = ctx.pop().unwrap().1;
    let codomain = maybe_codomain?;
    Ok(pi(domain, codomain))
}

fn assert_type(
    actual: Expression,
    expected: Expression,
) -> Result<(), TypeCheckError> {
    if actual.clone().reduces_to(expected.clone())
        || expected.clone().reduces_to(actual.clone())
    {
        Ok(())
    } else {
        let path = Vec::new();
        Err(TypeCheckError { path, expected, actual })
    }
}


fn type_check_apply(
    ctx: &mut Context,
    function: &typed::Expression,
    argument: &typed::Expression,
) -> Result<Expression, TypeCheckError> {
    use self::ErrorPath::*;
    let fun_type = type_check(ctx, function)
        .map_err(|err| err.with_context(InFunction))?;
    let arg_type = type_check(ctx, argument)
        .map_err(|err| err.with_context(InArgument))?;
    let (domain, codomain) = expect_pi_type(fun_type, &arg_type)
        .map_err(|err| err.with_context(InFunction))?;
    assert_type(arg_type, domain)
        .map_err(|err| err.with_context(InArgument))?;

    let codomain = codomain.substitute(&argument.convert());
    Ok(codomain)
}
fn expect_pi_type(fun_type: Expression, arg_type: &Expression)
    -> Result<(Expression, Expression), TypeCheckError>
{
    if let Expression::IntroType(ref maybe_pi) = fun_type {
        let maybe_pi = &**maybe_pi;
        if let Type::Pi { .. } = *maybe_pi {
            if let Expression::IntroType(maybe_pi) = fun_type {
                let maybe_pi = *maybe_pi;
                if let Type::Pi { domain, codomain } = maybe_pi {
                    return Ok((*domain, *codomain));
                }
            }
            unreachable!();
        }
    }
    let path = Vec::new();
    let domain = arg_type.clone();
    let expected = pi(domain, unit());
    let actual = fun_type;
    Err(TypeCheckError { path, expected, actual })
}

#[cfg(test)]
mod tests {
    use typed::*;
    use super::type_check;
    use super::TypeCheckError;
    use super::ErrorPath::*;

    macro_rules! type_checks {
        ($before: expr => $after: expr) => {{
            #![allow(unreachable_code, unused_variables)]
            let mut ctx = Vec::new();
            let before = $before;
            let after = type_check(&mut ctx, &before);
            assert_eq!(after, Ok($after.convert()));
            // mainly for `variable_management` but should always pass
            assert_eq!(*ctx, []);
        }}
    }

    macro_rules! type_error {
        ($expr: expr => $err: expr) => {{
            #![allow(unreachable_code, unused_variables)]
            let mut ctx = Vec::new();
            let expr = $expr;
            let err = type_check(&mut ctx, &expr);
            assert_eq!(err, Err($err));
            assert_eq!(*ctx, []);
        }}
    }

    #[test]
    fn discrete_type_checking() {
        type_checks!(point() => unit());

        type_checks!(tt() => bool());

        type_checks!(ff() => bool());

        type_checks!(
            if_then_else(tt(), point(), point(), unit())
        =>
            apply(lambda("_", bool(), unit()), tt())
        );

        type_error!(
            if_then_else(point(), tt(), tt(), bool())
        =>
            TypeCheckError {
                path: vec![InArgument],
                expected: bool().convert(),
                actual: unit().convert(),
            }
        );

        type_error!(
            if_then_else(tt(), tt(), point(), bool())
        =>
            TypeCheckError {
                path: vec![InArgument, InFunction],
                expected: apply(lambda("_", bool(), bool()), ff()).convert(),
                actual: unit().convert(),
            }
        );
    }

    #[test]
    fn function_type_checking() {
        type_checks!(lambda("x", unit(), var("x")) => pi("_", unit(), unit()));

        type_checks!(apply(lambda("_", bool(), point()), tt()) => unit());

        type_error!(
            apply(lambda("_", bool(), point()), point())
        =>
            TypeCheckError {
                path: vec![InArgument],
                expected: bool().convert(),
                actual: unit().convert(),
            }
        );

        type_error!(
            apply(point(), tt())
        =>
            TypeCheckError {
                path: vec![InFunction],
                expected: pi("_", bool(), unit()).convert(),
                actual: unit().convert(),
            }
        );
    }

    #[test]
    fn pair_type_checking() {
        type_checks!(
            pair(point(), tt(), unit(), bool())
        =>
            sigma("_", unit(), bool())
        );

        type_checks!(
            uncurry_fn(void(), unit(), bool())
        =>
            pi("_", pi("_", void(), pi("_", unit(), bool())),
              pi("_", sigma("_", void(), unit()),
                bool()
            ))
        );
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &point());
        assert_eq!(*ctx, []);

        type_checks!(
            // \x: Unit -> \y: Bool -> <y, x>
            lambda("x", unit(), lambda("y", bool(),
                pair(bool(), unit(), var("y"), var("x"))
            ))
        =>
            // Unit -> Bool -> Bool * Unit
            pi("_", unit(), pi("_", bool(), sigma("_", bool(), unit())))
        );
    }

    #[test]
    fn annotation_checks() {
        // `()` is not a type
        type_error!(
            pair_fn(point(), point())
        =>
            unimplemented!()
        );

        type_error!(
            lambda("_", point(), point())
        =>
            unimplemented!()
        );

        type_error!(
            if_then_else_fn(point())
        =>
            unimplemented!()
        );
    }

    #[test]
    fn dependent_types() {
        // this type family is useful
        let tf = || if_then_else(var("d"), bool(), unit(), universe());

        type_checks!(
            lambda(
                "d",
                bool(),
                apply(
                    lambda(
                        "_",
                        unit(),
                        if_then_else(
                            // if y then tt else ()
                            //   as (if y0 then bool else unit)
                            var("d"), tt(), point(), tf()
                        ),
                    ),
                    point()
                )
            )
        =>
            // if y then bool else unit
            pi("d", bool(), tf())
        );

        type_checks!(
            // \x: Bool -> \y: (if x then Bool else Unit) -> <x, y>
            lambda("d", bool(),
                lambda("x", tf(),
                    pair(bool(), tf(), var("d"), var("x"))
            ))
        =>
            pi("d", bool(), pi("_", tf(), sigma("d", bool(), tf())))
        );

        type_checks!(
            // \A: U -> \B: U -> \x: A -> <tt, x>
            //   as (if t0 then A else B)
            lambda(
                "A",
                universe(),
                lambda(
                    "B",
                    universe(),
                    lambda(
                        "x",
                        var("A"),
                        pair(
                            tt(), var("x"),
                            bool(),
                            if_then_else(
                                var("d"),
                                var("A"),
                                var("B"),
                                universe(),
                            ),
                        )
                    )
                )
            )
        =>
            // forall A: U, forall B: U,
            //   A -> Sigma t: Bool, if t then A else B
            pi("A", universe(), pi("B", universe(),
                pi(
                    "_", var("A"), sigma("t", bool(),
                    if_then_else(var("t"), var("A"), var("B"), universe()))
                )
            ))
        )
    }

    #[test]
    fn inductive_types() {
        unimplemented!();
    }
}
