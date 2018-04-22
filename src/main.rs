extern crate lofer_lang;

use lofer_lang::untyped;

fn read_code(path: &str) -> untyped::Expression {
    unimplemented!();
}

fn main() {
    let mut args = ::std::env::args();
    args.next();  // first argument is executable itself

    let mut expr = untyped::lambda(untyped::var(0));
    for path in args {
        let next_expr = read_code(&path);
        expr = untyped::apply(expr, next_expr);
    }

    let result = expr.reduce();

    println!("Result:\n  {:?}", result);
}
