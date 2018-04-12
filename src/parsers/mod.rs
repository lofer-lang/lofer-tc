mod readable;

#[cfg(test)]
mod tests {
    use super::readable;

    macro_rules! parses {
        ($parser: expr, $text: expr) => {{
            let parser = $parser;
            let original = $text;
            let parsed = parser.parse(original).unwrap();
            let regenerated = format!("{}", parsed);
            assert_eq!(regenerated, original);
        }}
    }

    #[test]
    fn parses() {
        let expr_parser = readable::ExprParser::new();
        parses!(expr_parser, "a b (c d)");
    }
}

