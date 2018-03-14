use programs::*;
use expressions;
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

pub fn type_check(ctx: &mut Context, expr: &expressions::Expression)
    -> Result<Expression, TypeCheckError>
{
    use expressions::Expression::*;
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

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckError {
    InLambda(TypeCheckLambdaError),
    InApply(TypeCheckApplyError),
}

impl From<TypeCheckLambdaError> for TypeCheckError {
    fn from(val: TypeCheckLambdaError) -> Self {
        TypeCheckError::InLambda(val)
    }
}

impl From<TypeCheckApplyError> for TypeCheckError {
    fn from(val: TypeCheckApplyError) -> Self {
        TypeCheckError::InApply(val)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeError {
    Err(Box<TypeCheckError>),
    Mismatch {
        expected: Expression,
        actual: Expression,
    },
}

impl From<TypeCheckError> for TypeError {
    fn from(err: TypeCheckError) -> Self {
        TypeError::Err(Box::new(err))
    }
}

fn type_check_lambda(
    ctx: &mut Context,
    var_name: &String,
    var_type: &expressions::Expression,
    body: &expressions::Expression,
) -> Result<Expression, TypeCheckLambdaError> {
    ctx.push((var_name.clone(), var_type.convert()));
    let maybe_codomain = type_check(ctx, body);
    let domain = ctx.pop().unwrap().1;
    let codomain = maybe_codomain?;
    Ok(pi(domain, codomain))
}

#[derive(PartialEq, Debug, Clone)]
pub struct TypeCheckLambdaError {
    in_body: Box<TypeCheckError>
}

impl From<TypeCheckError> for TypeCheckLambdaError {
    fn from(in_body: TypeCheckError) -> Self {
        let in_body = Box::new(in_body);
        TypeCheckLambdaError { in_body }
    }
}

fn assert_type(
    ctx: &mut Context,
    val: &expressions::Expression,
    expected: &Expression,
) -> Result<(), TypeError> {
    let actual = type_check(ctx, val)?;
    let expected = expected.clone();

    if actual.clone().reduces_to(expected.clone())
        || expected.clone().reduces_to(actual.clone())
    {
        Ok(())
    } else {
        Err(TypeError::Mismatch { expected, actual })
    }
}

fn type_check_apply(
    ctx: &mut Context,
    function: &expressions::Expression,
    argument: &expressions::Expression,
) -> Result<Expression, TypeCheckApplyError> {
    use self::TypeCheckApplyError::*;

    let fun_type = type_check(ctx, function)
        .map_err(|err| InFunction(Box::new(err)))?;
    let fun_type = fun_type.reduce_weak();
    if let Expression::IntroType(maybe_pi) = fun_type {
        let maybe_pi = *maybe_pi;
        if let Type::Pi { domain, codomain } = maybe_pi {
            assert_type(ctx, argument, &*domain)
                .map_err(|err| Argument(err))?;
            let codomain = codomain.substitute(&argument.convert());
            Ok(codomain)
        } else {
            Err(FunctionNotPi(simple_type(maybe_pi)))
        }
    } else {
        Err(FunctionNotPi(fun_type))
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckApplyError {
    InFunction(Box<TypeCheckError>),
    FunctionNotPi(Expression),
    Argument(TypeError),
}

#[cfg(test)]
mod tests {
    use expressions::*;
    use super::type_check;
    use super::{TypeCheckError, TypeCheckApplyError, TypeCheckLambdaError,
       TypeError};

    macro_rules! type_checks {
        ($before: expr => $after: expr) => {{
            #![allow(unreachable_code, unused_variables)]
            let mut ctx = Vec::new();
            let before = $before;
            let after = type_check(&mut ctx, &before);
            assert_eq!(Ok($after.convert()), after);
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
            assert_eq!(Err($err), err);
            assert_eq!(*ctx, []);
        }}
    }

    #[test]
    fn discrete_type_checking() {
        type_checks!(point() => unit());

        type_checks!(tt() => bool());

        type_checks!(ff() => bool());

        type_checks!(if_then_else(tt(), point(), point(), unit()) => unit());

        type_error!(
            if_then_else(point(), tt(), tt(), bool())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::Argument(
                    TypeError::Mismatch {
                        expected: unit().convert(),
                        actual: unit().convert(),
                    }
                )
            )
        /*
            TypeCheckError::InIf(
                TypeCheckIfError::Condition(
                    TypeError::Mismatch {
                        expected: bool(),
                        actual: unit(),
                    }
                )
            )
            */
        );

        type_error!(
            if_then_else(tt(), tt(), point(), bool())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::Argument(
                    TypeError::Mismatch {
                        expected: unit().convert(),
                        actual: unit().convert(),
                    }
                )
            )
        /*
            TypeCheckError::InIf(
                TypeCheckIfError::FFBranch(
                    TypeError::Mismatch {
                        expected: bool(),
                        actual: unit(),
                    }
                )
            )
            */
        );
    }

    #[test]
    fn function_type_checking() {
        type_checks!(lambda("x", unit(), var("x")) => pi("_", unit(), unit()));

        type_checks!(apply(lambda("_", bool(), point()), tt()) => unit());

        type_error!(
            apply(lambda("_", bool(), point()), point())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::Argument(
                    TypeError::Mismatch {
                        expected: bool().convert(),
                        actual: unit().convert(),
                    }
                )
            )
        );

        type_error!(
            apply(point(), tt())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::FunctionNotPi(unit().convert())
            )
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
