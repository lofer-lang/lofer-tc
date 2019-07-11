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
    let annotation = convert_expr(&mut Default::default(), annotation.typ.clone());
    let (bindings, result) = split_ctx_output(annotation, fun.definition.vars.len());
    let mut ctx = NameChain::with_names(var_names.clone());
    let body = convert_expr(&mut ctx, fun.definition.body.clone());
    type_check_expr(&body, &bindings, result);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ident {
    //Postulate(usize),
    //Global(usize),
    Local(usize),
}

#[derive(Clone, PartialEq)]
enum Expr {
    Type,
    Arrow(Vec<Expr>),
    Alg { head: Ident, tail: Vec<Expr> },
}

type Context = Vec<Expr>;

#[derive(Default)]
struct NameChain<'a> {
    prev_size: usize,
    prev: Option<&'a NameChain<'a>>,
    this: Vec<String>,
}

impl<'a> NameChain<'a> {
    fn with_names(this: Vec<String>) -> Self {
        NameChain { this, ..Default::default() }
    }
    fn push(self: &'a Self) -> Self {
        NameChain {
            prev_size: self.size(),
            prev: Some(self),
            this: Vec::new(),
        }
    }
    fn size(self: &Self) -> usize {
        self.prev_size + self.this.len()
    }

    fn get_index(self: &Self, name: &str) -> Option<usize> {
        let mut curr = self;
        loop {
            let mut result = curr.this.len();
            while result > 0 {
                result -= 1;
                if curr.this[result] == name {
                    return Some(result + curr.prev_size);
                }
            }
            if let Some(prev) = &curr.prev {
                curr = prev;
            } else {
                return None;
            }
        }
    }
}

fn convert_expr(ctx: &NameChain, expr: ast::Expr)
    -> Expr
{
    match expr {
        ast::Expr::Arrow(ast::ArrowExpr { params, output }) => {
            let mut out = Vec::new();
            let mut ctx = ctx.push();
            for (name, ty) in params {
                ctx.this.push(name.unwrap_or("_".into()));
                out.push(convert_expr(&ctx, ty));
            }
            // TODO detect arrow to arrow and merge
            out.push(convert_expr(&ctx, *output));
            Expr::Arrow(out)
        },
        ast::Expr::Alg(ast::AlgExpr { head, tail }) => {
            let head = {
                if let Some(id) = ctx.get_index(&head) {
                    Ident::Local(id)
                } else if head == "Type" {
                    if tail.len() > 0 {
                        panic!("cannot apply term `Type` of type `Type` to arguments");
                    } else {
                        return Expr::Type;
                    }
                } else {
                    panic!("Could not find term for identifier: {}", head);
                }
            };
            let tail = tail
                .into_iter()
                .map(|ex| convert_expr(ctx, ex))
                .collect();
            // TODO test whether function needs to be evaluated
            Expr::Alg { head, tail }
        },
    }
}

fn split_ctx_output_vec(mut ctx: Vec<Expr>, n: usize) -> (Context, Expr) {
    if ctx.len() > n + 1 {
        let terms = ctx.drain(n..).collect();
        (ctx, Expr::Arrow(terms))
    } else if ctx.len() == n + 1 {
        let output = ctx.pop().unwrap();
        (ctx, output)
    } else { // ctx.len() < n + 1
        panic!("Too many parameters for given annotation");
    }
}

fn split_ctx_output(expr: Expr, n: usize) -> (Context, Expr) {
    if let Expr::Arrow(ends) = expr {
        split_ctx_output_vec(ends, n)
    } else {
        if n == 0 {
            (Vec::new(), expr)
        } else {
            panic!("Too many parameters for given annotation. (not expecting any)");
        }
    }
}

fn type_check_expr(
    expr: &Expr,
    ctx: &Context,
    expected: Expr,
) {
    let actual = determine_type(expr, ctx);
    // @Completeness evaluate actual and expected first?
    if actual != expected {
        panic!("Types did not match");
    }
}

// figures out the type of an expression,
// while also checking that function applications are valid
fn determine_type(
    expr: &Expr,
    ctx: &Context,
) -> Expr {
    match expr {
        Expr::Type => Expr::Type,
        Expr::Arrow(ends) => {
            for each in ends {
                type_check_expr(each, ctx, Expr::Type);
            }
            Expr::Type
        },
        Expr::Alg{head, tail} => {
            let mut checked = 0;
            let mut expr_ty = match *head {
                Ident::Local(i) => {
                    ctx[i].clone()
                },
            };
            while checked < tail.len() {
                match expr_ty {
                    Expr::Arrow(ends) => {
                        while checked < tail.len() && checked < ends.len() - 1 {
                            // @Memory maybe subst could take &mut param?
                            // @Performance skip this cloning operation if i is 0?
                            let param_ty = subst(
                                &ends[checked],
                                &tail[0..checked],
                                ctx.len()
                            );
                            type_check_expr(&tail[checked], ctx, param_ty);
                            checked += 1;
                        }
                        if checked < ends.len() - 1 {
                            expr_ty = Expr::Arrow(ends[checked..].to_owned());
                        } else { // checked == ends.len() - 1
                            expr_ty = {ends}.pop().unwrap();
                        }
                        expr_ty = subst(&expr_ty, &tail[0..checked], ctx.len());
                    },
                    Expr::Alg { head, tail } => {
                        // attempt to reduce and if it can't be reduced complain
                        unimplemented!();
                    },
                    Expr::Type => {
                        panic!("Cannot apply type to arguments");
                    },
                }
            }
            expr_ty
        },
    }
}

fn subst(expr: &Expr, args: &[Expr], ctx_size: usize) -> Expr {
    match expr {
        Expr::Type => Expr::Type,
        Expr::Arrow(ends) => {
            let mut new_ends = Vec::with_capacity(ends.len());
            for end in ends {
                // I love non-relative indexing
                new_ends.push(subst(end, args, ctx_size));
            }
            Expr::Arrow(new_ends)
        },
        Expr::Alg { head, tail } => {
            let mut result = match *head {
                Ident::Local(i) => {
                    if i < ctx_size {
                        Expr::Alg {
                            head: Ident::Local(i),
                            tail: Vec::with_capacity(tail.len()),
                        }
                    } else if i - ctx_size < args.len() {
                        args[i - ctx_size].clone()
                    } else {
                        Expr::Alg {
                            head: Ident::Local(i - args.len()),
                            tail: Vec::with_capacity(tail.len()),
                        }
                    }
                },
            };
            if tail.len() > 0 {
                if let Expr::Alg { tail: new_tail, .. } = &mut result {
                    for expr in tail {
                        new_tail.push(subst(expr, args, ctx_size));
                    }
                } else {
                    panic!("Substituted type into head position... cannot apply type to arguments");
                }
            }
            result
        },
    }
}
