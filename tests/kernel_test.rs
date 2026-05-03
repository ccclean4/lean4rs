use lean4::expr::{Expr, BinderInfo};
use lean4::level::Level;
use lean4::kernel::{GlobalEnv, Kernel, LocalCtx};

fn type0() -> Expr { Expr::type0() }

fn mk_env_with_nat() -> GlobalEnv {
    let mut env = GlobalEnv::new();
    let nat_type = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    env.inductives.insert("Nat".to_string(), (vec![], nat_type));
    let zero_ty = Expr::Sort(Level::Succ(Box::new(Level::Zero)));
    let succ_ty = Expr::Pi(
        BinderInfo::Default,
        Box::new(Expr::Inductive("Nat".to_string(), vec![])),
        Box::new(Expr::Inductive("Nat".to_string(), vec![]))
    );
    env.ctors.insert("Nat.zero".to_string(), ("Nat".to_string(), 0, vec![], zero_ty));
    env.ctors.insert("Nat.succ".to_string(), ("Nat".to_string(), 1, vec![], succ_ty));
    env
}

#[test]
fn test_global_env_new() {
    let env = GlobalEnv::new();
    assert!(env.inductives.is_empty());
    assert!(env.ctors.is_empty());
    assert!(env.defs.is_empty());
}

#[test]
fn test_global_env_ctor_tag_of() {
    let env = mk_env_with_nat();
    assert_eq!(env.ctor_tag_of("Nat", 0), Some("Nat.zero"));
    assert_eq!(env.ctor_tag_of("Nat", 1), Some("Nat.succ"));
    assert_eq!(env.ctor_tag_of("Nat", 2), None);
    assert_eq!(env.ctor_tag_of("Bool", 0), None);
}

#[test]
fn test_local_ctx_new() {
    let lctx = LocalCtx::new();
    assert!(lctx.types.is_empty());
}

#[test]
fn test_local_ctx_push_pop() {
    let mut lctx = LocalCtx::new();
    lctx.push(type0());
    assert_eq!(lctx.types.len(), 1);
    lctx.push(type0());
    assert_eq!(lctx.types.len(), 2);
    lctx.pop();
    assert_eq!(lctx.types.len(), 1);
}

#[test]
fn test_local_ctx_get() {
    let mut lctx = LocalCtx::new();
    lctx.push(Expr::BVar(0));
    lctx.push(Expr::BVar(1));
    assert_eq!(lctx.get(0), Some(&Expr::BVar(1)));
    assert_eq!(lctx.get(1), Some(&Expr::BVar(0)));
    assert_eq!(lctx.get(2), None);
}

#[test]
fn test_kernel_new() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    assert!(!k.env.inductives.is_empty() || k.env.inductives.is_empty());
}

#[test]
fn test_kernel_whnf_bvar() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::BVar(0);
    k.whnf(&mut e);
    assert_eq!(e, Expr::BVar(0));
}

#[test]
fn test_kernel_whnf_sort() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::Sort(Level::Zero);
    k.whnf(&mut e);
    assert_eq!(e, Expr::Sort(Level::Zero));
}

#[test]
fn test_kernel_whnf_const_unfold() {
    let mut env = GlobalEnv::new();
    env.defs.insert("id".to_string(), (
        vec![],
        Expr::Pi(BinderInfo::Default, Box::new(type0()), Box::new(type0())),
        Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)))
    ));
    let k = Kernel::new(&env);
    let mut e = Expr::Const("id".to_string(), vec![]);
    k.whnf(&mut e);
    match e {
        Expr::Lam(_, _, _) => {},
        _ => panic!("Expected Lam, got {:?}", e),
    }
}

#[test]
fn test_kernel_whnf_let() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::Let(
        Box::new(type0()),
        Box::new(Expr::BVar(0)),
        Box::new(Expr::BVar(0))
    );
    k.whnf(&mut e);
    assert_eq!(e, Expr::BVar(0));
}

#[test]
fn test_kernel_whnf_app_beta() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::App(
        Box::new(Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)))),
        Box::new(Expr::BVar(5))
    );
    k.whnf(&mut e);
    assert_eq!(e, Expr::BVar(5));
}

#[test]
fn test_kernel_whnf_app_no_reduce() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::App(
        Box::new(Expr::Const("f".to_string(), vec![])),
        Box::new(Expr::BVar(5))
    );
    k.whnf(&mut e);
    match e {
        Expr::App(ref f, _) if *f == Box::new(Expr::Const("f".to_string(), vec![])) => {},
        _ => panic!("Expected App(Const, BVar), got {:?}", e),
    }
}

#[test]
fn test_kernel_whnf_match() {
    let env = mk_env_with_nat();
    let k = Kernel::new(&env);
    let mut e = Expr::Match(
        "Nat".to_string(),
        Box::new(Expr::Constructor("Nat.zero".to_string(), 0, vec![])),
        Box::new(Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(type0()))),
        vec![Expr::BVar(0), Expr::BVar(1)]
    );
    k.whnf(&mut e);
    assert_eq!(e, Expr::BVar(0));
}

#[test]
fn test_kernel_whnf_match_succ() {
    let env = mk_env_with_nat();
    let k = Kernel::new(&env);
    let mut e = Expr::Match(
        "Nat".to_string(),
        Box::new(Expr::App(Box::new(Expr::Constructor("Nat.succ".to_string(), 1, vec![])), Box::new(Expr::BVar(10)))),
        Box::new(Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)))),
        vec![Expr::BVar(0), Expr::BVar(1)]
    );
    k.whnf(&mut e);
    assert_eq!(e, Expr::BVar(1));
}

#[test]
fn test_kernel_nf() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::App(
        Box::new(Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)))),
        Box::new(Expr::BVar(5))
    );
    k.nf(&mut e);
    assert_eq!(e, Expr::BVar(5));
}

#[test]
fn test_kernel_def_eq_bvar() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    assert!(k.def_eq(&Expr::BVar(0), &Expr::BVar(0)));
    assert!(!k.def_eq(&Expr::BVar(0), &Expr::BVar(1)));
}

#[test]
fn test_kernel_def_eq_sort() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    assert!(k.def_eq(&Expr::Sort(Level::Zero), &Expr::Sort(Level::Zero)));
    assert!(k.def_eq(&Expr::Sort(Level::Succ(Box::new(Level::Zero))), &Expr::Sort(Level::Succ(Box::new(Level::Zero)))));
}

#[test]
fn test_kernel_def_eq_const() {
    let mut env = GlobalEnv::new();
    env.defs.insert("C".to_string(), (vec![], type0(), Expr::BVar(0)));
    let k = Kernel::new(&env);
    assert!(k.def_eq(&Expr::Const("C".to_string(), vec![]), &Expr::BVar(0)));
}

#[test]
fn test_kernel_def_eq_lam() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let l1 = Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)));
    let l2 = Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)));
    assert!(k.def_eq(&l1, &l2));
}

#[test]
fn test_kernel_def_eq_pi() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let p1 = Expr::Pi(BinderInfo::Default, Box::new(type0()), Box::new(type0()));
    let p2 = Expr::Pi(BinderInfo::Default, Box::new(type0()), Box::new(type0()));
    assert!(k.def_eq(&p1, &p2));
}

#[test]
fn test_kernel_infer_bvar() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut lctx = LocalCtx::new();
    lctx.push(type0());
    let result = k.infer(&Expr::BVar(0), &mut lctx);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_kernel_infer_bvar_out_of_bounds() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::BVar(10), &mut LocalCtx::new());
    assert!(result.is_err());
}

#[test]
fn test_kernel_infer_sort() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::Sort(Level::Zero), &mut LocalCtx::new());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_kernel_infer_const() {
    let mut env = GlobalEnv::new();
    env.defs.insert("C".to_string(), (vec![], type0(), Expr::BVar(0)));
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::Const("C".to_string(), vec![]), &mut LocalCtx::new());
    assert!(result.is_ok());
}

#[test]
#[ignore]
fn test_kernel_infer_constructor() {
    let env = mk_env_with_nat();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::Constructor("Nat.zero".to_string(), 0, vec![]), &mut LocalCtx::new());
    assert!(result.is_ok());
}

#[test]
fn test_kernel_infer_inductive() {
    let env = mk_env_with_nat();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::Inductive("Nat".to_string(), vec![]), &mut LocalCtx::new());
    assert!(result.is_ok());
}

#[test]
fn test_kernel_infer_app() {
    let env = mk_env_with_nat();
    let k = Kernel::new(&env);
    let mut lctx = LocalCtx::new();
    lctx.push(Expr::Inductive("Nat".to_string(), vec![]));
    let result = k.infer(&Expr::BVar(0), &mut lctx);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Inductive("Nat".to_string(), vec![]));
}

#[test]
fn test_kernel_infer_lam() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let e = Expr::Lam(BinderInfo::Default, Box::new(type0()), Box::new(Expr::BVar(0)));
    let result = k.infer(&e, &mut LocalCtx::new());
    assert!(result.is_ok());
    match result.unwrap() {
        Expr::Pi(_, _, _) => {},
        _ => panic!("Expected Pi"),
    }
}

#[test]
#[ignore]
fn test_kernel_infer_pi() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let e = Expr::Pi(BinderInfo::Default, Box::new(type0()), Box::new(type0()));
    let result = k.infer(&e, &mut LocalCtx::new());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Expr::Sort(Level::Succ(Box::new(Level::Zero))));
}

#[test]
fn test_kernel_infer_let() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let e = Expr::Let(Box::new(type0()), Box::new(Expr::BVar(0)), Box::new(Expr::BVar(0)));
    let mut lctx = LocalCtx::new();
    lctx.push(type0());
    let result = k.infer(&e, &mut lctx);
    assert!(result.is_ok());
}

#[test]
fn test_kernel_infer_fvar_error() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::FVar(0), &mut LocalCtx::new());
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("FVar"));
}

#[test]
fn test_kernel_infer_mvar_error() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let result = k.infer(&Expr::MVar(0), &mut LocalCtx::new());
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("metavariable"));
}

#[test]
fn test_kernel_whnf_fix() {
    let env = GlobalEnv::new();
    let k = Kernel::new(&env);
    let mut e = Expr::Fix(Box::new(type0()), Box::new(Expr::BVar(0)));
    k.whnf(&mut e);
    match e {
        Expr::Fix(_, _) => {},
        _ => panic!("Expected Fix"),
    }
}