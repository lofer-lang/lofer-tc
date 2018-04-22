pub mod readable;
pub mod readable_programs;

#[cfg(test)]
mod tests {
    use super::readable;
    use super::readable_programs;

    macro_rules! parses {
        ($parser: expr, $text: expr) => {{
            let parser = &$parser;
            let original = $text;
            let parsed = parser.parse(original).unwrap();
            let regenerated = format!("{}", parsed);
            assert_eq!(regenerated, original);
        }}
    }

    macro_rules! builtin {
        ($parser: expr, $text: expr) => {{
            let parser = &$parser;
            let original = $text;
            let parsed = parser.parse(original).unwrap();

            {
                let head = &*parsed.head;
                if let ::readable::HeadExpression::Name(ref name) = *head {
                    panic!("Not builtin: {}", name);
                }
            }

            let regenerated = format!("{}", parsed);
            assert_eq!(regenerated, original);
        }}
    }

    macro_rules! parses_single {
        ($parser: expr, $text: expr) => {{
            let parser = &$parser;
            let original = $text;
            let parsed = parser.parse(original).unwrap();
            assert!(parsed.len() == 1, "Only test one program at a time");
            let regenerated = format!("{}", parsed[0]);
            assert_eq!(regenerated, original);
        }}
    }

    #[test]
    fn expr_parsing() {
        let parser = readable::ExprParser::new();
        parses!(parser, "a b (c d)");
    }

    #[test]
    fn builtins() {
        let parser = readable::ExprParser::new();
        builtin!(parser, "void_elim result");

        builtin!(parser, "tt");
        builtin!(parser, "unit_elim family");

        builtin!(parser, "true");
        builtin!(parser, "false");
        builtin!(parser, "bool_elim family");

        builtin!(parser, "pair fst snd_fam");
        builtin!(parser, "sigma_elim fst snd_fam out_fam");

        builtin!(parser, "Void");
        builtin!(parser, "Unit");
        builtin!(parser, "Bool");
        builtin!(parser, "Sigma x: A, B x");
        builtin!(parser, "Pi x: A, B x");
        builtin!(parser, "Type");

        builtin!(parser, "fix A");

        parses!(parser, "Pi x: (Pi y: A, B y), C x");
        parses!(parser, "Sigma x: A, Sigma y: B x, C x y");
    }

    #[test]
    fn function_parsing() {
        let parser = readable::FunParser::new();
        parses!(parser, "id (x: T) = x");
        parses!(parser, "const (x: T) (y: U) = x");
        parses!(parser, "inl (x: T) = pair true x");
    }

    #[test]
    fn program_parsing() {
        let parser = readable_programs::ProgramParser::new();
        parses_single!(parser, "id (x: T) = x\n");
        parses_single!(parser, "\
output = pair T U x y
  U (_x: V) = bool_elim _U Unit _x
    _U (_: Bool) = Type\n");
    }
}

