use std::iter;

use readable;
use parsers;

pub struct ProgramParser(parsers::readable::FunParser);

fn count_indent(line: &str) -> usize {
    let mut result = 0;
    for c in line.chars() {
        if c == ' ' {
            result += 1;
        } else {
            return result;
        }
    }
    result
}

struct IndentedCode<'a> {
    line: &'a str,
    sublines: Vec<IndentedCode<'a>>,
}

fn split_indenting<'a, I>(input: I) -> Vec<IndentedCode<'a>>
    where I: Iterator<Item=&'a str>
{
    let mut peek_input = input.peekable();
    split_indenting_helper(&mut peek_input, 0)
}

fn split_indenting_helper<'a, I>(
    input: &mut iter::Peekable<I>,
    min_indent: usize,
) -> Vec<IndentedCode<'a>>
    where I: Iterator<Item=&'a str>
{
    let curr_indent = |input: &mut iter::Peekable<I>| {
        let mut result = None;
        loop {
            if let Some(line) = input.peek() {
                let count = count_indent(*line);
                if count != line.len() {
                    result = Some(count);
                    break;
                }
            } else {
                // no lines left, return None
                break;
            }
            // empty/whitespace line, skip
            input.next();
        }
        result
    };

    let mut result = Vec::new();

    let indent = curr_indent(input);

    if indent.is_none() {
        return result;
    }

    let indent = indent.unwrap();

    if indent < min_indent {
        return result;
    }

    while curr_indent(input) == Some(indent) {
        let line = input.next().unwrap();
        let sublines = split_indenting_helper(input, indent + 1);
        let next = IndentedCode { line, sublines };
        result.push(next);
    }
    result
}

type Error<'a> = ::lalrpop_util::ParseError<usize,
    parsers::readable::Token<'a>, &'a str>;

impl ProgramParser {
    pub fn new() -> Self {
        let inner = parsers::readable::FunParser::new();

        ProgramParser(inner)
    }

    pub fn parse<'a>(self: &Self, input: &'a str)
        -> Result<Vec<readable::Program>, Error<'a>>
    {
        let indented = split_indenting(input.split("\n"));
        self.from_indented(indented)
    }

    fn from_indented<'a>(self: &Self, indented: Vec<IndentedCode<'a>>)
        -> Result<Vec<readable::Program>, Error<'a>>
    {
        let mut result = Vec::with_capacity(indented.len());

        for indented in indented {
            let output = self.0.parse(indented.line)?;
            let associated = self.from_indented(indented.sublines)?;
            let program = readable::Program { output, associated };
            result.push(program);
        }

        Ok(result)
    }
}

