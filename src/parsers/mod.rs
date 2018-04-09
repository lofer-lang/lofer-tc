mod typed;

#[test]
fn parses() {
    assert_eq!(typed::TermParser::new().parse("(123)"), Ok(123));
}

