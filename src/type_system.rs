use expressions::*;

type TypeCheckError = ();

pub fn type_check(ctx: &mut Vec<Expression>, expr: &Expression)
    -> Result<Expression, TypeCheckError>
{
    unimplemented!();
}
/*
    use expressions::Expression::*;
    match *expr {
        Variable(i) => {
            // was deepen but need to change to named variables
            unimplemented!();
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
            Ok(type_check_if(ctx, condition, tt_branch, ff_branch, out_type)?)
        },

        IntroLambda { ref in_type, ref body } => {
            Ok(type_check_lambda(ctx, in_type, body)?)
        },
        ElimApplication { ref function, ref argument } => {
            Ok(type_check_apply(ctx, function, argument)?)
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            Ok(type_check_pair(ctx, fst, snd, snd_type)?)
        },
        ElimFst { ref pair } => {
            Ok(type_check_fst(ctx, pair)
               .map_err(|err| TypeCheckError::InFst(err))?)
        },
        ElimSnd { ref pair } => {
            Ok(type_check_snd(ctx, pair)
               .map_err(|err| TypeCheckError::InSnd(err))?)
        },

        IntroType(_) => {
            // TODO check types properly :P
            Ok(universe())
        },

        SpecialFix { ref generator } => {
            Ok(type_check_fix(ctx, generator, expr)?)
        },
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckError {
    InIf(TypeCheckIfError),
    InLambda(TypeCheckLambdaError),
    InApply(TypeCheckApplyError),
    InPair(TypeCheckPairError),
    InFst(TypeCheckPairElimError),
    InSnd(TypeCheckPairElimError),
    InFix(TypeCheckFixError),
}

impl From<TypeCheckIfError> for TypeCheckError {
    fn from(val: TypeCheckIfError) -> Self {
        TypeCheckError::InIf(val)
    }
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

impl From<TypeCheckPairError> for TypeCheckError {
    fn from(val: TypeCheckPairError) -> Self {
        TypeCheckError::InPair(val)
    }
}

impl From<TypeCheckFixError> for TypeCheckError {
    fn from(val: TypeCheckFixError) -> Self {
        TypeCheckError::InFix(val)
    }
}

fn assert_type(
    ctx: &mut Vec<Expression>,
    val: &Expression,
    expected: &Expression,
) -> Result<(), TypeError> {
    let actual = type_check(ctx, val)?;
    //let actual = actual.reduce_lazy();
    //let expected = expected.reduce_lazy();
    let expected = expected.clone();
    if actual == expected {
        unimplemented!();
        Ok(())
    } else {
        Err(TypeError::Mismatch { expected, actual })
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

fn type_check_if(
    ctx: &mut Vec<Expression>,
    condition: &Expression,
    tt_branch: &Expression,
    ff_branch: &Expression,
    out_type: &Expression,
) -> Result<Expression, TypeCheckIfError> {
    use self::TypeCheckIfError::*;
    assert_type(ctx, condition, &bool())
        .map_err(|err| Condition(err))?;

    assert_type(ctx, tt_branch, &out_type.substitute(&tt()))
        .map_err(|err| TTBranch(err))?;
    assert_type(ctx, ff_branch, &out_type.substitute(&ff()))
        .map_err(|err| FFBranch(err))?;

    let out_type = out_type.substitute(condition);
    Ok(out_type)
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckIfError {
    Condition(TypeError),
    TTBranch(TypeError),
    FFBranch(TypeError),
}

fn type_check_lambda(
    ctx: &mut Vec<Expression>,
    in_type: &Expression,
    body: &Expression,
) -> Result<Expression, TypeCheckLambdaError> {
    ctx.push(in_type.clone());
    let maybe_codomain = type_check(ctx, body);
    let domain = ctx.pop().unwrap();
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

fn type_check_apply(
    ctx: &mut Vec<Expression>,
    function: &Expression,
    argument: &Expression,
) -> Result<Expression, TypeCheckApplyError> {
    use self::TypeCheckApplyError::*;

    let fun_type = type_check(ctx, function)
        .map_err(|err| InFunction(Box::new(err)))?;
    let fun_type = fun_type.reduce_lazy();
    if let Expression::IntroType(maybe_pi) = fun_type {
        let maybe_pi = *maybe_pi;
        if let Type::Pi { domain, codomain } = maybe_pi {
            assert_type(ctx, argument, &*domain)
                .map_err(|err| Argument(err))?;
            let codomain = codomain.substitute(&argument);
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

fn type_check_pair(
    ctx: &mut Vec<Expression>,
    fst: &Expression,
    snd: &Expression,
    snd_type: &Expression,
) -> Result<Expression, TypeCheckPairError> {
    use self::TypeCheckPairError::*;
    let fst_type = type_check(ctx, fst)
        .map_err(|err| InFst(Box::new(err)))?;
    let expected_snd_type = snd_type.substitute(fst);
    assert_type(ctx, snd, &expected_snd_type)
        .map_err(|err| Snd(err))?;
    Ok(sigma(fst_type, snd_type.clone()))
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckPairError {
    InFst(Box<TypeCheckError>),
    Snd(TypeError),
}

fn type_check_pair_elim(ctx: &mut Vec<Expression>, pair: &Expression)
    -> Result<(Expression, Expression), TypeCheckPairElimError>
{
    use self::TypeCheckPairElimError::*;
    let pair_type = type_check(ctx, pair)
        .map_err(|err| InPair(Box::new(err)))?;
    let pair_type = pair_type.reduce_lazy();
    if let Expression::IntroType(maybe_sigma) = pair_type {
        let maybe_sigma = *maybe_sigma;
        if let Type::Sigma { fst_type, snd_type } = maybe_sigma {
            Ok((*fst_type, *snd_type))
        } else {
            Err(NotSigma(simple_type(maybe_sigma)))
        }
    } else {
        Err(NotSigma(pair_type))
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckPairElimError {
    InPair(Box<TypeCheckError>),
    NotSigma(Expression),
}

fn type_check_fst(ctx: &mut Vec<Expression>, pair: &Expression)
    -> Result<Expression, TypeCheckPairElimError>
{
    Ok(type_check_pair_elim(ctx, pair)?.0)
}

fn type_check_snd(ctx: &mut Vec<Expression>, pair: &Expression)
    -> Result<Expression, TypeCheckPairElimError>
{
    let snd_type = type_check_pair_elim(ctx, pair)?.1;
    let pair = pair.clone();
    let pair = Box::new(pair);
    let fst = Expression::ElimFst { pair };
    let snd_type = snd_type.substitute(&fst);
    Ok(snd_type)
}

fn type_check_fix(
    ctx: &mut Vec<Expression>,
    generator: &Expression,
    fixed_point: &Expression
) -> Result<Expression, TypeCheckFixError>
{
    use self::TypeCheckFixError::*;
    let generator_type = type_check(ctx, generator)
        .map_err(|err| InGenerator(Box::new(err)))?;
    if let Expression::IntroType(maybe_pi) = generator_type {
        let maybe_pi = *maybe_pi;
        if let Type::Pi { domain, codomain } = maybe_pi {
            let codomain = codomain.substitute(fixed_point);
            // are these necessary? probably?
            let domain = domain.reduce_lazy();
            let codomain = codomain.reduce_lazy();
            if domain == codomain {
                Ok(domain)
            } else {
                Err(NotEndo { domain, codomain })
            }
        } else {
            Err(NotPi(simple_type(maybe_pi)))
        }
    } else {
        Err(NotPi(generator_type))
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeCheckFixError {
    InGenerator(Box<TypeCheckError>),
    NotPi(Expression),
    /// Given a generator `gen`, the fixed point `fix gen` can only
    /// exist if the the domain of `gen` is the type of `gen (fix gen)`.
    /// In the absence of dependently typed functions, this means the
    /// domain and codomain must be equal, i.e. the generator function must
    /// be an endofunction.
    NotEndo {
        domain: Expression,
        codomain: Expression,
    },
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! type_checks {
        ($before: expr => $after: expr) => {{
            #![allow(unreachable_code, unused_variables)]
            let mut ctx = Vec::new();
            let before = $before;
            let after = type_check(&mut ctx, &before);
            assert_eq!(Ok($after), after);
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
            TypeCheckError::InIf(
                TypeCheckIfError::Condition(
                    TypeError::Mismatch {
                        expected: bool(),
                        actual: unit(),
                    }
                )
            )
        );

        type_error!(
            if_then_else(tt(), tt(), point(), bool())
        =>
            TypeCheckError::InIf(
                TypeCheckIfError::FFBranch(
                    TypeError::Mismatch {
                        expected: bool(),
                        actual: unit(),
                    }
                )
            )
        );
    }

    #[test]
    fn function_type_checking() {
        type_checks!(lambda(unit(), var(0)) => pi(unit(), unit()));

        type_checks!(apply(lambda(bool(), point()), tt()) => unit());

        type_error!(
            apply(lambda(bool(), point()), point())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::Argument(
                    TypeError::Mismatch {
                        expected: bool(),
                        actual: unit(),
                    }
                )
            )
        );

        type_error!(
            apply(point(), tt())
        =>
            TypeCheckError::InApply(
                TypeCheckApplyError::FunctionNotPi(unit())
            )
        );
    }

    #[test]
    fn pair_type_checking() {
        type_checks!(pair(point(), tt(), bool()) => sigma(unit(), bool()));

        type_checks!(fst(pair(point(), tt(), bool())) => unit());

        type_checks!(snd(pair(point(), tt(), bool())) => bool());

        let err = || TypeCheckPairElimError::NotSigma(unit());

        type_error!(fst(point()) => TypeCheckError::InFst(err()));

        type_error!(snd(point()) => TypeCheckError::InSnd(err()));
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &Expression::IntroPoint);
        assert_eq!(*ctx, []);

        type_checks!(
            // \x: Unit -> \y: Bool -> <y, x>
            lambda(unit(), lambda(bool(), pair(var(0), var(1), unit())))
        =>
            // Unit -> Bool -> Bool * Unit
            pi(unit(), pi(bool(), sigma(bool(), unit())))
        );
    }

    #[test]
    fn annotation_checks() {
        // `()` is not a type
        type_error!(
            pair(point(), point(), point())
        =>
            unimplemented!()
        );

        type_error!(
            lambda(point(), point())
        =>
            unimplemented!()
        );

        type_error!(
            pair(point(), point(), point())
        =>
            unimplemented!()
        );
    }

    #[test]
    fn dependent_types() {
        // this type family is useful
        let tf = || if_then_else(var(0), bool(), unit(), universe());

        type_checks!(
            lambda(
                bool(),
                apply(
                    lambda(
                        unit(),
                        if_then_else(
                            // if y then tt else ()
                            //   as (if y0 then bool else unit)
                            var(1), tt(), point(), tf()
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
            lambda(bool(), lambda(tf(), pair(var(1), var(0), tf())))
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
                        var(1),
                        pair(
                            tt(), var(0),
                            if_then_else(var(0), var(3), var(2), universe())
                        )
                    )
                )
            )
        =>
            // forall A: U, forall B: U,
            //   A -> Sigma t: Bool, if t then A else U
            pi(universe(), pi(universe(),
                pi(
                    var(1), sigma(bool(),
                    if_then_else(var(0), var(3), var(2), universe()))
                )
            ))
        )
    }

    #[test]
    fn inductive_types() {
        unimplemented!();
    }
}

