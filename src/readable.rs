use std::fmt;

pub struct Program {
    pub output: Function,
    pub associated: Vec<Program>,
}

pub struct Function {
    pub fname: String,
    pub vars: Vec<Var>,
    pub body: Expression,
}

pub struct Var {
    pub name: String,
    pub typ: Expression,
}

pub struct Expression {
    pub head: Box<HeadExpression>,
    pub tail: Vec<Expression>,
}

pub enum HeadExpression {
    Name(String),

    VoidElim(Expression),

    Point,
    UnitElim(Expression),

    True,
    False,
    BoolElim(Expression),

    Pair(Expression, Expression),
    SigmaElim(Expression, Expression, Expression),

    Void,
    Unit,
    Bool,
    Sigma(String, Expression, Expression),
    Pi(String, Expression, Expression),
    Type,

    Fix(Expression),
}

impl fmt::Display for Program {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.display_with_indent(0, f)
    }
}

impl Program {
    fn display_with_indent(self: &Self, indent: usize, f: &mut fmt::Formatter)
        -> Result<(), fmt::Error>
    {
        write!(f, "{:indent$}{}\n", "", self.output, indent=indent)?;
        for subprogram in &self.associated {
            subprogram.display_with_indent(indent + 2, f)?;
        }
        Ok(())
    }
}

impl fmt::Display for Function {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.fname)?;
        for var in &self.vars {
            write!(f, " ({})", var)?;
        }
        write!(f, " = {}", self.body)?;
        Ok(())
    }
}

impl fmt::Display for Var {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl fmt::Display for Expression {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.head)?;
        for arg in &self.tail {
            if arg.tail.len() == 0 {
                write!(f, " {}", arg)?;
            } else {
                write!(f, " ({})", arg)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for HeadExpression {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::HeadExpression::*;
        match *self {
            Name(ref name) => {
                write!(f, "{}", name)?;
            },

            _ => write!(f, "?")?,
        }
        Ok(())
    }
}
