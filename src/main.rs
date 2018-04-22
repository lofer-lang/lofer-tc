extern crate lofer_lang;

use std::fs::File;
use std::io::prelude::*;

use lofer_lang::conversion;
use lofer_lang::parsers;
use lofer_lang::untyped;

fn read_code(parser: &parsers::ProgramParser, path: &str)
    -> untyped::Expression
{
    let mut file = File::open(path).expect("Failed to open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents).expect("Failed to read file");

    let programs = parser.parse(&contents).expect("Failed to parse file");
    conversion::convert(programs)
}

fn main() {
    let mut args = ::std::env::args();
    args.next();  // first argument is executable itself

    let parser = parsers::ProgramParser::new();

    let mut expr = untyped::lambda(untyped::var(0));
    for path in args {
        let next_expr = read_code(&parser, &path);
        expr = untyped::apply(expr, next_expr);
    }

    let result = expr.reduce();

    println!("Result:\n  {:?}", result);
}
