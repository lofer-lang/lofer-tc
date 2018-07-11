use std::iter;

use readable;
use parsers;

pub struct ProgramParser(parsers::readable::LineParser);

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

struct IndentedCode {
    line: String,
    sublines: Vec<IndentedCode>,
}

fn split_indenting<'a, I>(input: I) -> Vec<IndentedCode>
    where I: Iterator<Item=&'a str>
{
    let mut peek_input = input.peekable();
    split_indenting_helper(&mut peek_input, 0)
}

// counts the indent of lines and returns the first indent that is smaller
// than the line length
// i.e. discards empty lines
fn find_line<'a, I>(input: &mut iter::Peekable<I>) -> Option<usize>
    where I: Iterator<Item=&'a str>
{
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
}

fn concat_lines<'a, I>(input: &mut iter::Peekable<I>) -> String
    where I: Iterator<Item=&'a str>
{
    let mut result = String::new();
    while find_line(input).is_some() {
        let line = input.next().unwrap();
        if line.chars().rev().next().unwrap() == '\\' {
            let line = line.get(..line.len() - 1).unwrap();
            result.push_str(line);
        } else {
            result.push_str(line);
            break;
        }
    }
    result
}

fn split_indenting_helper<'a, I>(
    input: &mut iter::Peekable<I>,
    min_indent: usize,
) -> Vec<IndentedCode>
    where I: Iterator<Item=&'a str>
{
    let mut result = Vec::new();

    let indent = find_line(input);

    if indent.is_none() {
        return result;
    }

    let indent = indent.unwrap();

    if indent < min_indent {
        return result;
    }

    while find_line(input) == Some(indent) {
        let line = concat_lines(input);
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
        let inner = parsers::readable::LineParser::new();

        ProgramParser(inner)
    }

    pub fn parse<'a>(self: &Self, input: &'a str)
        -> Vec<readable::Program>
    {
        let indented = split_indenting(input.split("\n"));
        self.from_indented(&indented).unwrap() // can't return the error
             // because it would outlive the thing being parsed
             // by switching IndentedCode back to str/Vec<str> we could
             // fix that?
             // but we can't parse functions from a Vec<str>
             // so we'd actually need to refactor the parser somehow
             // id rather just not report errors and save that for the
             // self hosting parser
    }

    fn from_indented<'a>(self: &Self, indented: &'a Vec<IndentedCode>)
        -> Result<Vec<readable::Program>, Error<'a>>
    {
        let mut result = Vec::with_capacity(indented.len());

        for indented in indented {
            let output = self.0.parse(&indented.line)?;
            if let readable::Line::Function(output) = output {
                let associated = self.from_indented(&indented.sublines)?;
                let program = readable::Program { output, associated };
                result.push(program);
            }
        }

        Ok(result)
    }
}

