use lean4::elaborator::{Elaborator, PreExpr, PreLevel};
use lean4::expr::{Expr, BinderInfo};
use lean4::level::Level;

#[test]
fn test_elaborator_new() {
    let elab = Elaborator::new();
    assert!(elab.env.inductives.is_empty());
    assert!(elab.env.ctors.is_empty());
    assert!(elab.env.defs.is_empty());
}

#[test]
fn test_elaborator_elab_hole() {
    let mut elab = Elaborator::new();
    let result = elab.elab(&PreExpr::Hole, None, &[]);
    assert!(result.is_ok());
    match result.unwrap() {
        Expr::MVar(_) => {},
        _ => panic!("Expected MVar"),
    }
}

#[test]
fn test_elaborator_elab_nat_lit_zero() {
    let mut elab = Elaborator::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    elab.env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let result = elab.elab(&PreExpr::NatLit(0), None, &[]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Constructor("Nat".to_string(), 0, vec![]));
}

#[test]
fn test_elaborator_elab_nat_lit_three() {
    let mut elab = Elaborator::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    elab.env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let result = elab.elab(&PreExpr::NatLit(3), None, &[]);
    assert!(result.is_ok());
    let e = result.unwrap();
    match e {
        Expr::App(ref f, ref a) => {
            assert_eq!(**f, Expr::Constructor("Nat".to_string(), 1, vec![]));
            match a.as_ref() {
                Expr::App(ref g, ref b) => {
                    assert_eq!(**g, Expr::Constructor("Nat".to_string(), 1, vec![]));
                    match b.as_ref() {
                        Expr::App(h, c) => {
                            assert_eq!(**h, Expr::Constructor("Nat".to_string(), 1, vec![]));
                            assert_eq!(**c, Expr::Constructor("Nat".to_string(), 0, vec![]));
                        },
                        _ => panic!("Expected App at innermost"),
                    }
                },
                _ => panic!("Expected nested App at second level"),
            }
        },
        _ => panic!("Expected App at top level"),
    }
}

#[test]
fn test_elaborator_elab_sort() {
    let mut elab = Elaborator::new();
    let result = elab.elab(&PreExpr::Sort(PreLevel::Nat(0)), None, &[]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Zero));
}

#[test]
fn test_elaborator_elab_sort_type() {
    let mut elab = Elaborator::new();
    let result = elab.elab(&PreExpr::Sort(PreLevel::Nat(1)), None, &[]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_elaborator_elab_sort_with_param() {
    let mut elab = Elaborator::new();
    let result = elab.elab(&PreExpr::Sort(PreLevel::Param("u".to_string())), None, &["u".to_string()]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Param("u".to_string())));
}

#[test]
fn test_elaborator_elab_var_unknown() {
    let mut elab = Elaborator::new();
    let result = elab.elab(&PreExpr::Var("unknown".to_string()), None, &[]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("Unknown identifier"));
}

#[test]
fn test_elaborator_elab_lam() {
    let mut elab = Elaborator::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    elab.env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let body = PreExpr::Var("x".to_string());
    let lam = PreExpr::Lam(BinderInfo::Default, "x".to_string(), Box::new(PreExpr::Sort(PreLevel::Nat(1))), Box::new(body));
    let result = elab.elab(&lam, None, &[]);
    assert!(result.is_ok());
    match result.unwrap() {
        Expr::Lam(_, ty, body) => {
            assert_eq!(*ty, Expr::Sort(Level::Succ(Box::new(Level::Zero))));
            assert_eq!(*body, Expr::BVar(0));
        },
        _ => panic!("Expected Lam"),
    }
}

#[test]
fn test_elaborator_elab_pi() {
    let mut elab = Elaborator::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    elab.env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let body = PreExpr::Var("x".to_string());
    let pi = PreExpr::Pi(BinderInfo::Default, "x".to_string(), Box::new(PreExpr::Sort(PreLevel::Nat(1))), Box::new(body));
    let result = elab.elab(&pi, None, &[]);
    assert!(result.is_ok());
    match result.unwrap() {
        Expr::Pi(_, ty, body) => {
            assert_eq!(*ty, Expr::Sort(Level::Succ(Box::new(Level::Zero))));
            assert_eq!(*body, Expr::BVar(0));
        },
        _ => panic!("Expected Pi"),
    }
}

#[test]
fn test_elaborator_elab_var_nat_type() {
    let mut elab = Elaborator::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    elab.env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let result = elab.elab(&PreExpr::Var("Nat".to_string()), None, &[]);
    assert!(result.is_ok());
    match result.unwrap() {
        Expr::Inductive(name, lvls) => {
            assert_eq!(name, "Nat");
            assert!(lvls.is_empty());
        },
        _ => panic!("Expected Inductive"),
    }
}