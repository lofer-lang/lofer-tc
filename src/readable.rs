use std::fmt;

pub struct Program {
    pub output: Function,
    pub associated: Vec<Program>,
}

pub enum Line {
    Function(Function),
    Annotation(Annotation),
}

pub struct Function {
    pub fname: String,
    pub vars: Vec<Annotation>,
    pub body: Expression,
}

pub struct Annotation {
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

impl fmt::Display for Annotation {
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

            VoidElim(ref output) => {
                write!(f, "void_elim {}", output)?;
            },

            Point => {
                write!(f, "tt")?;
            },
            UnitElim(ref output) => {
                write!(f, "unit_elim {}", output)?;
            },

            True => {
                write!(f, "true")?;
            },
            False => {
                write!(f, "false")?;
            },
            BoolElim(ref family) => {
                write!(f, "bool_elim {}", family)?;
            },

            Pair(ref fst, ref snd_family) => {
                write!(f, "pair {} {}", fst, snd_family)?;
            }
            SigmaElim(ref fst, ref snd_family, ref output) => {
                write!(f, "sigma_elim {} {} {}", fst, snd_family, output)?;
            }

            Void => {
                write!(f, "Void")?;
            },
            Unit => {
                write!(f, "Unit")?;
            },
            Bool => {
                write!(f, "Bool")?;
            },
            Sigma(ref name, ref fst, ref snd_family) => {
                write!(f, "Sigma {}: ", name)?;
                comma_free_print(fst, f)?;
                write!(f, ", {}", snd_family)?;
            },
            Pi(ref name, ref arg, ref output_family) => {
                write!(f, "Pi {}: ", name)?;
                comma_free_print(arg, f)?;
                write!(f, ", {}", output_family)?;
            },
            Type => {
                write!(f, "Type")?;
            },

            Fix(ref output) => {
                write!(f, "fix {}", output)?;
            },
        }
        Ok(())
    }
}

// prints, but adds brackets if the expression has a comma
fn comma_free_print(expr: &Expression, f: &mut fmt::Formatter)
    -> Result<(), fmt::Error>
{
    use readable::HeadExpression::*;
    match *expr.head {
        Pi(..) | Sigma(..) =>
            write!(f, "({})", expr)?,
        _ =>
            write!(f, "{}", expr)?,
    }
    Ok(())
}

