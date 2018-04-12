mod readable;

#[test]
fn parses() {
    assert_eq!(readable::ExprParser::new().parse("a b (c d)"), ());
}

