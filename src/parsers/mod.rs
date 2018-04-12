mod readable;

#[cfg(test)]
mod tests {
    use super::readable;

    macro_rules! parses {
        ($parser: expr, $text: expr) => {{
            let parser = &$parser;
            let original = $text;
            let parsed = parser.parse(original).unwrap();
            let regenerated = format!("{}", parsed);
            assert_eq!(regenerated, original);
        }}
    }

    #[test]
    fn expr_parsing() {
        let parser = readable::ExprParser::new();
        parses!(parser, "a b (c d)");
    }

    #[test]
    fn function_parsing() {
        let parser = readable::FunParser::new();
        parses!(parser, "id (x: T) = x");
        parses!(parser, "const (x: T) (y: U) = x");
        parses!(parser, "inl (x: T) = Pair true x");
    }
}

