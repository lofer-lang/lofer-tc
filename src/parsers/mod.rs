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

        parses!(parser, "void_elim result");

        parses!(parser, "tt");
        parses!(parser, "unit_elim family");

        parses!(parser, "true");
        parses!(parser, "false");
        parses!(parser, "bool_elim family");

        parses!(parser, "pair fst snd_fam");
        parses!(parser, "sigma_elim fst snd_fam out_fam");
    }

    #[test]
    fn function_parsing() {
        let parser = readable::FunParser::new();
        parses!(parser, "id (x: T) = x");
        parses!(parser, "const (x: T) (y: U) = x");
        parses!(parser, "inl (x: T) = Pair true x");
    }

    #[test]
    fn program_parsing() {
        let parser = readable_programs::ProgramParser::new();
        parses_single!(parser, "id (x: T) = x\n");
        parses_single!(parser, "\
output = Pair T U x y
  U (_x: V) = bool_elim _U Unit _x
    _U (_: Bool) = Type\n");
    }
}

