use readable;
use untyped;

pub fn convert(programs: Vec<readable::Program>)
    -> untyped::Expression
{
    let mut ctx = Vec::new();
    let mut results = convert_programs(programs, &mut ctx);
    debug_assert!(ctx.len() == 0, "Context improperly handled");
    let inner = results.pop().unwrap().1;
    wrap_redeces(inner, results)
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
        let extra_ctx = convert_programs(program.associated, ctx);
        ctx.push(extra_ctx);
        let (name, expr) = convert_fun(program.output, ctx);
        let associated = ctx.pop().unwrap();
        result = ctx.pop().unwrap();
        let expr = wrap_redeces(expr, associated);
        result.push((name, expr));
    }

    result
}

fn convert_fun(fun: readable::Function, ctx: &mut Vec<Vec<Term>>) -> Term {
    let vars = fun.vars
        .into_iter()
        .map(|var| (var.name, untyped::unit()))
        .collect();
    ctx.push(vars);
    let mut body = convert_body(fun.body, ctx);

    let vars = ctx.pop().unwrap();
    for _ in vars {
        body = untyped::lambda(body);
    }

    (fun.fname, body)
}

fn convert_body(body: readable::Expression, ctx: &mut Vec<Vec<Term>>)
    -> untyped::Expression
{
    let mut result = convert_head(body.head, ctx);
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
            let parser = ::parsers::readable_programs::ProgramParser::new();
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
}
