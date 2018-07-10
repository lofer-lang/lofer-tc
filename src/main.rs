extern crate lofer_lang;

use std::fs::File;
use std::io::prelude::*;

use lofer_lang::conversion;
use lofer_lang::parsers;
use lofer_lang::readable;

fn read_code(parser: &parsers::ProgramParser, path: &str)
    -> Vec<readable::Program>
{
    let mut file = File::open(path).expect("Failed to open file");
    let mut contents = String::new();
    file.read_to_string(&mut contents).expect("Failed to read file");

    let programs = parser.parse(&contents).expect("Failed to parse file");
    programs
}

fn main() {
    let mut args = ::std::env::args();
    args.next();  // first argument is executable itself

    let parser = parsers::ProgramParser::new();

    let programses = args.map(|path| read_code(&parser, &path)).collect();
    let expr = conversion::convert(programses);

    let result = expr.reduce();

    println!("Result:\n  {:?}", result);
}
