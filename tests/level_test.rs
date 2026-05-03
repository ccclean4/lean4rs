use lean4::level::Level;

#[test]
fn test_level_of_nat() {
    assert_eq!(Level::of_nat(0), Level::Zero);
    assert_eq!(Level::of_nat(1), Level::Succ(Box::new(Level::Zero)));
    assert_eq!(Level::of_nat(3), Level::Succ(Box::new(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))))));
}

#[test]
fn test_level_succ_pretty() {
    assert_eq!(Level::Succ(Box::new(Level::Zero)).pretty(), "1");
    assert_eq!(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))).pretty(), "2");
}

#[test]
fn test_level_max_equal() {
    let l = Level::Max(Box::new(Level::Zero), Box::new(Level::Zero));
    assert_eq!(l.normalize(), Level::Zero);
}

#[test]
fn test_level_max_different() {
    let l = Level::Max(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Zero));
    let norm = l.normalize();
    assert_eq!(norm, Level::Max(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Zero)));
}

#[test]
fn test_level_imax_zero() {
    let l = Level::IMax(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Zero));
    assert_eq!(l.normalize(), Level::Zero);
}

#[test]
fn test_level_imax_nonzero() {
    let l = Level::IMax(Box::new(Level::Zero), Box::new(Level::Succ(Box::new(Level::Zero))));
    let norm = l.normalize();
    assert_eq!(norm, Level::IMax(Box::new(Level::Zero), Box::new(Level::Succ(Box::new(Level::Zero)))));
}

#[test]
fn test_level_imax_same() {
    let l = Level::IMax(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Succ(Box::new(Level::Zero))));
    let norm = l.normalize();
    assert_eq!(norm, Level::Succ(Box::new(Level::Zero)));
}

#[test]
fn test_level_to_nat_zero() {
    assert_eq!(Level::Zero.to_nat(), Some(0));
}

#[test]
fn test_level_to_nat_succ() {
    assert_eq!(Level::Succ(Box::new(Level::Zero)).to_nat(), Some(1));
    assert_eq!(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))).to_nat(), Some(2));
}

#[test]
fn test_level_to_nat_max() {
    let l = Level::Max(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))))));
    assert_eq!(l.to_nat(), Some(2));
}

#[test]
fn test_level_to_nat_imax() {
    let l = Level::IMax(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))))));
    assert_eq!(l.to_nat(), Some(2));
}

#[test]
fn test_level_to_nat_imax_zero() {
    let l = Level::IMax(Box::new(Level::Succ(Box::new(Level::Zero))), Box::new(Level::Zero));
    assert_eq!(l.to_nat(), Some(0));
}

#[test]
fn test_level_to_nat_uvariate() {
    assert_eq!(Level::UVar("x".to_string()).to_nat(), None);
}

#[test]
fn test_level_to_nat_param() {
    assert_eq!(Level::Param("u".to_string()).to_nat(), None);
}

#[test]
fn test_level_subst_param() {
    let l = Level::Param("u".to_string());
    assert_eq!(l.subst_param("u", &Level::Succ(Box::new(Level::Zero))), Level::Succ(Box::new(Level::Zero)));
}

#[test]
fn test_level_subst_param_no_match() {
    let l = Level::Param("v".to_string());
    assert_eq!(l.subst_param("u", &Level::Succ(Box::new(Level::Zero))), Level::Param("v".to_string()));
}

#[test]
fn test_level_subst_param_nested() {
    let l = Level::Max(Box::new(Level::Param("u".to_string())), Box::new(Level::Succ(Box::new(Level::Param("u".to_string())))));
    let result = l.subst_param("u", &Level::of_nat(2));
    assert_eq!(result, Level::Max(Box::new(Level::of_nat(2)), Box::new(Level::Succ(Box::new(Level::of_nat(2))))));
}

#[test]
fn test_level_subst_uvar() {
    let l = Level::UVar("x".to_string());
    assert_eq!(l.subst_uvar("x", &Level::Succ(Box::new(Level::Zero))), Level::Succ(Box::new(Level::Zero)));
}

#[test]
fn test_level_subst_uvar_no_match() {
    let l = Level::UVar("y".to_string());
    assert_eq!(l.subst_uvar("x", &Level::Succ(Box::new(Level::Zero))), Level::UVar("y".to_string()));
}

#[test]
fn test_level_subst_uvar_nested() {
    let l = Level::Succ(Box::new(Level::UVar("x".to_string())));
    let result = l.subst_uvar("x", &Level::of_nat(3));
    assert_eq!(result, Level::Succ(Box::new(Level::of_nat(3))));
}

#[test]
fn test_level_pretty() {
    assert_eq!(Level::Zero.pretty(), "0");
    assert_eq!(Level::Succ(Box::new(Level::Zero)).pretty(), "1");
    assert_eq!(Level::Param("u".to_string()).pretty(), "u");
    assert_eq!(Level::UVar("x".to_string()).pretty(), "?x");
}

#[test]
fn test_level_pretty_max() {
    let l = Level::Max(Box::new(Level::Param("u".to_string())), Box::new(Level::Param("v".to_string())));
    assert_eq!(l.pretty(), "max u v");
}

#[test]
fn test_level_pretty_imax() {
    let l = Level::IMax(Box::new(Level::Param("u".to_string())), Box::new(Level::Param("v".to_string())));
    assert_eq!(l.pretty(), "imax u v");
}

#[test]
fn test_level_pretty_nested() {
    let l = Level::Succ(Box::new(Level::Max(Box::new(Level::Param("u".to_string())), Box::new(Level::Zero))));
    assert_eq!(l.pretty(), "(max u 0 + 1)");
}

#[test]
fn test_level_normalize_preserves_succ() {
    let l = Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero))));
    assert_eq!(l.normalize(), Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))));
}

#[test]
fn test_level_normalize_idempotent() {
    let l = Level::Max(Box::new(Level::Zero), Box::new(Level::Zero));
    assert_eq!(l.normalize(), l.normalize().normalize());
}