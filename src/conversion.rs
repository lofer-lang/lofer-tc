use readable;
use untyped;

pub fn convert(programs: Vec<Vec<readable::Program>>)
    -> untyped::Expression
{
    let mut ctx = vec![vec![]];
    for program in programs {
        let mut result_ctx = convert_programs(program, &mut ctx);
        debug_assert!(ctx.len() == 1, "Context improperly handled");
        let result = wrap_redeces_1(result_ctx);
        ctx[0].push(result);
    }
    let final_result = wrap_redeces_1(ctx.pop().unwrap());
    final_result.1
}

fn wrap_redeces_1(mut vals: Vec<Term>) -> Term {
    let (name, val_open) = vals.pop().unwrap();
    let val_closed = wrap_redeces(val_open, vals);
    (name, val_closed)
}

fn wrap_redeces(mut inner: untyped::Expression, mut ctx: Vec<Term>)
    -> untyped::Expression
{
    while let Some((_, term)) = ctx.pop() {
        inner = untyped::apply(untyped::lambda(inner), term);
    }

    inner
}

/*
 * Terms describe a named expression
 * each term is defined in terms of previous ones
 * so var(0) in one term refers to the term before it (when flattened)
 * var(1) to the term before that and so on
 *
 * when removing a term from the context, it must be reapplied somehow
 * which means wrapping the term it defined, in beta redeces
 * or in simple lambda abstractions
 */
type Term = (String, untyped::Expression);
fn convert_programs(programs: Vec<readable::Program>, ctx: &mut Vec<Vec<Term>>)
    -> Vec<Term>
{
    let mut result = Vec::new();

    for program in programs {
        ctx.push(result);
        let (name, expr) = convert_fun(program, ctx);
        result = ctx.pop().unwrap();
        result.push((name, expr));
    }

    result
}

fn convert_fun(program: readable::Program, ctx: &mut Vec<Vec<Term>>) -> Term {
    let vars = program.output.vars
        .into_iter()
        .map(|var| (var.name, untyped::unit()))
        .collect();
    ctx.push(vars);

    let mut expr = {
        let associated = convert_programs(program.associated, ctx);
        ctx.push(associated);
        let body = convert_body(program.output.body, ctx);

        let associated = ctx.pop().unwrap();
        wrap_redeces(body, associated)
    };

    let vars = ctx.pop().unwrap();
    for _ in vars {
        expr = untyped::lambda(expr);
    }

    (program.output.fname, expr)
}

fn convert_body(body: readable::Expression, ctx: &mut Vec<Vec<Term>>)
    -> untyped::Expression
{
    let mut result = convert_head(*body.head, ctx);
    for arg in body.tail {
        let arg = convert_body(arg, ctx);
        result = untyped::apply(result, arg);
    }
    result
}

fn convert_head(head: readable::HeadExpression, ctx: &mut Vec<Vec<Term>>)
    -> untyped::Expression
{
    use readable::HeadExpression::*;
    match head {
        Name(name) => untyped::var(get_var_id(name, ctx)),

        VoidElim(..) => untyped::absurd(),

        Point => untyped::point(),
        UnitElim(..) => untyped::trivial(),

        True => untyped::tt(),
        False => untyped::ff(),
        BoolElim(..) => untyped::Expression::ElimIf,

        Pair(..) => untyped::Expression::IntroPair,
        SigmaElim(..) => untyped::Expression::ElimUncurry,

        Fix(..) => untyped::lambda(untyped::fix(untyped::var(1))),

        // Type info is for typed systems
        _ => untyped::point(),
    }
}

fn get_var_id(name: String, ctx: &Vec<Vec<Term>>) -> usize {
    ctx.iter()
       .flat_map(|terms| terms)
       .rev()
       .position(|term| term.0 == name.as_str())
       .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use untyped::*;

    macro_rules! converts {
        ($a: expr => $b: expr) => {{
            let as_str = $a;
            let parser = ::parsers::ProgramParser::new();
            let as_ast = parser.parse(as_str).unwrap();
            let expected = $b;
            let actual = convert(as_ast);
            assert_eq!(actual, expected);
        }}
    }

    #[test]
    fn conversion() {
        converts!("f (x: a) = x" => lambda(var(0)));
        converts!("\
I (x: a) = x
apply = I" => apply(lambda(var(0)), lambda(var(0))));
        converts!("\
f (x: a) = const
  const (y: b) = x" => lambda(apply(lambda(var(0)), lambda(var(1)))));
    }

    #[test]
    fn builtins() {
        converts!("x A = void_elim A" => lambda(absurd()));

        converts!("x = tt" => point());
        converts!("x A = unit_elim A" => lambda(trivial()));

        converts!("x = true" => tt());
        converts!("x = false" => ff());
        converts!("x A = bool_elim A" => lambda(
            Expression::ElimIf,
        ));

        converts!("x A B = pair A B" => lambda(lambda(
            Expression::IntroPair,
        )));
        converts!("x A B C = sigma_elim A B C" => lambda(lambda(lambda(
            Expression::ElimUncurry,
        ))));

        converts!("x A = fix A" => lambda(lambda(fix(var(1)))));
    }
}
