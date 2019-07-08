extern crate lofer_lang;

use std::fs::File;
use std::io::prelude::*;

fn read_code(parser: &lofer_lang::ProgramParser, path: &str)
    -> Vec<lofer_lang::ast::Item>
{
    let mut file = File::open(path).expect("Failed to open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents).expect("Failed to read file");

    let programs = parser.parse(&contents);
    programs
}

fn main() {
    let mut args = ::std::env::args();
    args.next();  // first argument is executable itself

    let parser = lofer_lang::ProgramParser::new();

    let programses: Vec<_> = args.map(|path| read_code(&parser, &path)).collect();
    //let expr = conversion::convert(programses);

    //let result = expr.reduce();

    //println!("Result:\n  {:?}", result);
}
