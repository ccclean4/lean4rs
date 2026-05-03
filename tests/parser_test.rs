use lean4::parser;

#[test]
fn test_tokenize_simple() {
    let tokens = parser::tokenize("def x : Nat := 0");
    assert_eq!(tokens, vec!["def", "x", ":", "Nat", ":=", "0"]);
}

#[test]
fn test_tokenize_arrows() {
    let tokens = parser::tokenize("Nat -> Nat");
    assert_eq!(tokens, vec!["Nat", "->", "Nat"]);
}

#[test]
fn test_tokenize_type_with_level() {
    let tokens = parser::tokenize("Type 1");
    assert_eq!(tokens, vec!["Type", "1"]);
}

#[test]
fn test_tokenize_binders() {
    let tokens = parser::tokenize("(x : Nat) -> Type");
    assert_eq!(tokens, vec!["(", "x", ":", "Nat", ")", "->", "Type"]);
}

#[test]
fn test_tokenize_implicit_binder() {
    let tokens = parser::tokenize("{x : Nat} -> Type");
    assert_eq!(tokens, vec!["{", "x", ":", "Nat", "}", "->", "Type"]);
}

#[test]
fn test_tokenize_instance_binder() {
    let tokens = parser::tokenize("[x : Nat] -> Type");
    assert_eq!(tokens, vec!["[", "x", ":", "Nat", "]", "->", "Type"]);
}

#[test]
fn test_tokenize_comments() {
    let tokens = parser::tokenize("def x : Nat := 0 -- this is a comment");
    assert_eq!(tokens, vec!["def", "x", ":", "Nat", ":=", "0"]);
}

#[test]
fn test_tokenize_multiline() {
    let src = "def x : Nat := 0\ndef y : Nat := 1";
    let tokens = parser::tokenize(src);
    assert!(tokens.contains(&"def".to_string()));
    assert!(tokens.contains(&"x".to_string()));
    assert!(tokens.contains(&"y".to_string()));
}

#[test]
fn test_tokenize_unicode_arrows() {
    let tokens = parser::tokenize("Nat → Nat");
    assert_eq!(tokens, vec!["Nat", "→", "Nat"]);
}

#[test]
fn test_tokenize_universe_params() {
    let tokens = parser::tokenize("def List.{u} : Sort u -> Type");
    assert_eq!(tokens, vec!["def", "List", ".", "{", "u", "}", ":", "Sort", "u", "->", "Type"]);
}

#[test]
fn test_tokenize_match() {
    let tokens = parser::tokenize("match x with | Nat.zero => 0");
    assert_eq!(tokens, vec!["match", "x", "with", "|", "Nat.zero", "=>", "0"]);
}

#[test]
fn test_tokenize_constructor() {
    let tokens = parser::tokenize("| Nat.succ : Nat -> Nat");
    assert_eq!(tokens, vec!["|", "Nat.succ", ":", "Nat", "->", "Nat"]);
}

#[test]
fn test_tokenize_nat_literal() {
    let tokens = parser::tokenize("123");
    assert_eq!(tokens, vec!["123"]);
}

#[test]
fn test_tokenize_fun() {
    let tokens = parser::tokenize("fun (x : Nat) => x");
    assert_eq!(tokens, vec!["fun", "(", "x", ":", "Nat", ")", "=>", "x"]);
}

#[test]
fn test_tokenize_fix() {
    let tokens = parser::tokenize("fix f : Nat -> Nat => f");
    assert_eq!(tokens, vec!["fix", "f", ":", "Nat", "->", "Nat", "=>", "f"]);
}

#[test]
fn test_tokenize_let() {
    let tokens = parser::tokenize("let x : Nat := 0 ; x");
    assert_eq!(tokens, vec!["let", "x", ":", "Nat", ":=", "0", ";", "x"]);
}