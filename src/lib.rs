#[macro_use]
extern crate lalrpop_util;

pub mod ast;
mod indent_parser;

// why am I even using lalrpop for such a simple grammar
// f : (x1: A) -> (x2: B) -> (x3: C) -> D
// f x1 x2 x3 = a (b c (d e) f) g h
lalrpop_mod!(line_parser);

pub use indent_parser::ProgramParser;

pub fn type_check_all(programs: Vec<ast::Item>) {
    for item in &programs {
        type_check_function(item);
    }
}

fn type_check_function(fun: &ast::Item) {
    for _ in &fun.associated {
        unimplemented!();
    }
    if fun.annotation.is_none() {
        if fun.definition.vars.len() > 0 {
            panic!("Terms with parameters must have a type annotation");
        } else {
            unimplemented!();
        }
    }
    let annotation = fun.annotation.as_ref().unwrap();
    if annotation.name != fun.definition.fname {
        panic!(
            "Annotation for {} was given alongside definition for {}",
            annotation.name,
            fun.definition.fname,
        );
    }
    let var_names = &fun.definition.vars;
    let annotation = convert_expr(annotation.typ.clone());
    let (bindings, result) = split_ctx_output(annotation, fun.definition.vars.len());
    let body = convert_expr(fun.definition.body.clone());
    type_check_expr(&body, bindings);
}

enum Ident {
    //Postulate(usize),
    //Global(usize),
    Local(usize),
}

enum Expr {
    Type,
    Arrow(Vec<Expr>),
    Alg { head: Ident, tail: Vec<Expr> },
}

type Context = Vec<Expr>;

// could sometimes get away with borrowing rest
fn convert_expr(mut rest: ast::Expr)
    -> Expr
{
    match rest {
        ast::Expr::Arrow(ast::ArrowExpr { mut params, output }) => {
            let mut out = Vec::new();
            for (name, ty) in params {
                out.push(convert_expr(ty));
            }
            // TODO detect arrow to arrow and merge
            out.push(convert_expr(*output));
            Expr::Arrow(out)
        },
        ast::Expr::Alg(ast::AlgExpr { head, tail }) => {
            let tail = tail.into_iter().map(convert_expr).collect();
            let head = unimplemented!();
            // TODO test whether function needs to be evaluated
            Expr::Alg { head, tail };
        },
    }
}

fn split_ctx_output(expr: Expr, n: usize) -> (Context, Expr) {
    if let Expr::Arrow(mut ctx) = expr {
        if ctx.len() > n + 1 {
            let terms = ctx.drain(n..).collect();
            (ctx, Expr::Arrow(terms))
        } else if ctx.len() == n + 1 {
            let output = ctx.pop().unwrap();
            (ctx, output)
        } else { // ctx.len() < n + 1
            panic!("Too many parameters for given annotation");
        }
    } else {
        if n == 0 {
            (Vec::new(), expr)
        } else {
            panic!("Too many parameters for given annotation. (not expecting any)");
        }
    }
}

fn get_index(vars: &Vec<String>, name: &str) -> Option<usize> {
    let mut result = vars.len();
    while result > 0 {
        result -= 1;
        if vars[result] == name {
            return Some(result);
        }
    }
    None
}

fn type_check_expr(
    expr: &Expr,
    ctx: Context,
) {
    unimplemented!();
}

