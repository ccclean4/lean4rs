use lean4::expr::{Expr, BinderInfo};
use lean4::level::Level;

fn type0() -> Expr { Expr::type0() }

#[test]
fn test_expr_constructors() {
    let _ = Expr::BVar(0);
    let _ = Expr::FVar(1);
    let _ = Expr::MVar(2);
    let _ = Expr::Sort(Level::Zero);
    let _ = Expr::Const("x".to_string(), vec![]);
    let _ = Expr::App(Box::new(Expr::BVar(0)), Box::new(Expr::BVar(1)));
    let _ = Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)));
    let _ = Expr::Pi(BinderInfo::Default, Box::new(type0()), Box::new(type0()));
    let _ = Expr::Let(Box::new(type0()), Box::new(Expr::BVar(0)), Box::new(Expr::BVar(0)));
    let _ = Expr::Fix(Box::new(type0()), Box::new(Expr::BVar(0)));
    let _ = Expr::Inductive("Nat".to_string(), vec![]);
    let _ = Expr::Constructor("Nat.zero".to_string(), 0, vec![]);
}

#[test]
fn test_expr_prop_type0() {
    assert_eq!(Expr::prop(), Expr::Sort(Level::Zero));
    assert_eq!(type0(), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_bvar_lift_above_threshold() {
    let mut e = Expr::BVar(5);
    e.lift(1, 3);
    assert_eq!(e, Expr::BVar(6));
}

#[test]
fn test_bvar_lift_below_threshold() {
    let mut e = Expr::BVar(2);
    e.lift(1, 5);
    assert_eq!(e, Expr::BVar(2));
}

#[test]
fn test_bvar_lift_zero_threshold() {
    let mut e = Expr::BVar(0);
    e.lift(1, 0);
    assert_eq!(e, Expr::BVar(1));
}

#[test]
fn test_bvar_lift_multiple() {
    let mut e = Expr::BVar(10);
    e.lift(5, 3);
    assert_eq!(e, Expr::BVar(15));
}

#[test]
fn test_lam_lift_body_inner_var() {
    let mut e = Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(1)));
    e.lift(1, 0);
    assert_eq!(e, Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(2))));
}

#[test]
fn test_app_lift() {
    let mut e = Expr::App(Box::new(Expr::BVar(0)), Box::new(Expr::BVar(5)));
    e.lift(2, 3);
    assert_eq!(e, Expr::App(Box::new(Expr::BVar(0)), Box::new(Expr::BVar(7))));
}

#[test]
fn test_bvar_subst_equal() {
    let mut e = Expr::BVar(0);
    e.subst(0, &Expr::BVar(5));
    assert_eq!(e, Expr::BVar(5));
}

#[test]
fn test_bvar_subst_greater() {
    let mut e = Expr::BVar(5);
    e.subst(3, &Expr::BVar(0));
    assert_eq!(e, Expr::BVar(4));
}

#[test]
fn test_bvar_subst_less() {
    let mut e = Expr::BVar(2);
    e.subst(5, &Expr::BVar(0));
    assert_eq!(e, Expr::BVar(2));
}

#[test]
fn test_app_subst_fn() {
    let mut e = Expr::App(Box::new(Expr::BVar(0)), Box::new(Expr::BVar(1)));
    e.subst(0, &Expr::Const("f".to_string(), vec![]));
    match e {
        Expr::App(f, a) => {
            assert_eq!(&*f, &Expr::Const("f".to_string(), vec![]));
            assert_eq!(&*a, &Expr::BVar(0));
        },
        _ => panic!("Expected App"),
    }
}

#[test]
fn test_sort_subst_levels() {
    let mut e = Expr::Sort(Level::Param("u".to_string()));
    e.subst_levels(&[("u".to_string(), Level::Succ(Box::new(Level::Zero)))]);
    assert_eq!(e, Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_const_subst_levels() {
    let mut e = Expr::Const("C".to_string(), vec![Level::Param("u".to_string()), Level::Param("v".to_string())]);
    e.subst_levels(&[("u".to_string(), Level::of_nat(1))]);
    assert_eq!(e, Expr::Const("C".to_string(), vec![Level::of_nat(1), Level::Param("v".to_string())]));
}

#[test]
fn test_inductive_subst_levels() {
    let mut e = Expr::Inductive("List".to_string(), vec![Level::Param("u".to_string())]);
    e.subst_levels(&[("u".to_string(), Level::of_nat(2))]);
    assert_eq!(e, Expr::Inductive("List".to_string(), vec![Level::of_nat(2)]));
}

#[test]
fn test_constructor_subst_levels() {
    let mut e = Expr::Constructor("Nat.succ".to_string(), 1, vec![Level::Param("u".to_string())]);
    e.subst_levels(&[("u".to_string(), Level::of_nat(3))]);
    assert_eq!(e, Expr::Constructor("Nat.succ".to_string(), 1, vec![Level::of_nat(3)]));
}

#[test]
fn test_mvar_subst() {
    let mut e = Expr::MVar(5);
    e.subst_mvar(5, &Expr::BVar(3));
    assert_eq!(e, Expr::BVar(3));
}

#[test]
fn test_mvar_subst_no_match() {
    let mut e = Expr::MVar(5);
    e.subst_mvar(3, &Expr::BVar(0));
    assert_eq!(e, Expr::MVar(5));
}

#[test]
fn test_app_subst_mvar() {
    let mut e = Expr::App(Box::new(Expr::MVar(0)), Box::new(Expr::MVar(1)));
    e.subst_mvar(0, &Expr::BVar(10));
    match e {
        Expr::App(f, _) => assert_eq!(&*f, &Expr::BVar(10)),
        _ => panic!("Expected App"),
    }
}

#[test]
fn test_sort_subst_uvar() {
    let mut e = Expr::Sort(Level::UVar("u".to_string()));
    e.subst_uvar("u", &Level::Succ(Box::new(Level::Zero)));
    assert_eq!(e, Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_sort_subst_uvar_no_match() {
    let mut e = Expr::Sort(Level::UVar("v".to_string()));
    e.subst_uvar("u", &Level::Succ(Box::new(Level::Zero)));
    assert_eq!(e, Expr::Sort(Level::UVar("v".to_string())));
}

#[test]
fn test_const_subst_uvar() {
    let mut e = Expr::Const("C".to_string(), vec![Level::UVar("x".to_string())]);
    e.subst_uvar("x", &Level::of_nat(5));
    assert_eq!(e, Expr::Const("C".to_string(), vec![Level::of_nat(5)]));
}

#[test]
fn test_get_app_fn_args_simple() {
    let e = Expr::App(Box::new(Expr::Const("f".to_string(), vec![])), Box::new(Expr::BVar(0)));
    let (fn_, args) = e.get_app_fn_args();
    assert_eq!(fn_, &Expr::Const("f".to_string(), vec![]));
    assert_eq!(args, vec![Expr::BVar(0)]);
}

#[test]
fn test_get_app_fn_args_nested() {
    let e = Expr::App(
        Box::new(Expr::App(Box::new(Expr::Const("f".to_string(), vec![])), Box::new(Expr::BVar(0)))),
        Box::new(Expr::BVar(1))
    );
    let (fn_, args) = e.get_app_fn_args();
    assert_eq!(fn_, &Expr::Const("f".to_string(), vec![]));
    assert_eq!(args, vec![Expr::BVar(0), Expr::BVar(1)]);
}

#[test]
fn test_get_app_fn_args_non_app() {
    let e = Expr::BVar(5);
    let (fn_, args) = e.get_app_fn_args();
    assert_eq!(fn_, &Expr::BVar(5));
    assert!(args.is_empty());
}

#[test]
fn test_match_equality() {
    let branches = vec![Expr::BVar(0), Expr::BVar(1)];
    let e1 = Expr::Match("Nat".to_string(), Box::new(Expr::BVar(0)), Box::new(type0()), branches.clone());
    let e2 = Expr::Match("Nat".to_string(), Box::new(Expr::BVar(0)), Box::new(type0()), branches);
    assert_eq!(e1, e2);
}

#[test]
fn test_fix_equality() {
    let e1 = Expr::Fix(Box::new(type0()), Box::new(Expr::BVar(0)));
    let e2 = Expr::Fix(Box::new(type0()), Box::new(Expr::BVar(0)));
    assert_eq!(e1, e2);
}

#[test]
fn test_binder_info_equality() {
    assert_eq!(BinderInfo::Default, BinderInfo::Default);
    assert_eq!(BinderInfo::Implicit, BinderInfo::Implicit);
    assert_eq!(BinderInfo::Instance, BinderInfo::Instance);
    assert_ne!(BinderInfo::Default, BinderInfo::Implicit);
}

#[test]
fn test_expr_clone() {
    let e = Expr::App(Box::new(Expr::BVar(0)), Box::new(Expr::BVar(1)));
    let e_clone = e.clone();
    assert_eq!(e, e_clone);
}

#[test]
fn test_sort_equality() {
    assert_eq!(Expr::Sort(Level::Zero), Expr::Sort(Level::Zero));
    assert_eq!(Expr::Sort(Level::Succ(Box::new(Level::Zero))), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
    assert_ne!(Expr::Sort(Level::Zero), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}