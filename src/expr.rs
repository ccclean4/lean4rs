use crate::level::Level;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    BVar(usize),
    FVar(usize),
    MVar(usize),
    Sort(Level),
    Const(String, Vec<Level>),
    App(Box<Expr>, Box<Expr>),
    Lam(BinderInfo, Box<Expr>, Box<Expr>),
    Pi(BinderInfo, Box<Expr>, Box<Expr>),
    Let(Box<Expr>, Box<Expr>, Box<Expr>),
    Fix(Box<Expr>, Box<Expr>),
    Inductive(String, Vec<Level>),
    Constructor(String, usize, Vec<Level>),
    Match(String, Box<Expr>, Box<Expr>, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinderInfo {
    Default,
    Implicit,
    Instance,
}

use Expr::*;
use BinderInfo::*;

impl Expr {
    pub fn prop() -> Expr { Sort(Level::Zero) }
    pub fn type0() -> Expr { Sort(Level::Succ(Box::new(Level::Zero))) }

    pub fn mk_arrow(a: Expr, mut b: Expr) -> Expr {
        b.lift(1, 0);
        Pi(BinderInfo::Default, Box::new(a), Box::new(b))
    }

    pub fn get_app_fn_args(&self) -> (&Expr, Vec<Expr>) {
        let mut curr = self;
        let mut args = Vec::new();
        while let App(f, arg) = curr { args.push(*arg.clone()); curr = f; }
        args.reverse();
        (curr, args)
    }

    pub fn lift(&mut self, amount: usize, threshold: usize) {
        match self {
            BVar(n) => { if *n >= threshold { *n += amount; } }
            FVar(_) | MVar(_) | Sort(_) | Inductive(_, _)
            | Constructor(_, _, _) | Const(_, _) => {}
            App(f, a) => { f.lift(amount, threshold); a.lift(amount, threshold); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                ty.lift(amount, threshold);
                body.lift(amount, threshold + 1);
            }
            Let(ty, val, body) => {
                ty.lift(amount, threshold);
                val.lift(amount, threshold);
                body.lift(amount, threshold + 1);
            }
            Match(_, target, motive, branches) => {
                target.lift(amount, threshold);
                motive.lift(amount, threshold + 1);
                for b in branches { b.lift(amount, threshold); }
            }
        }
    }

    pub fn subst(&mut self, var_idx: usize, value: &Expr) {
        match self {
            BVar(n) => {
                if *n == var_idx { *self = value.clone(); }
                else if *n > var_idx { *n -= 1; }
            }
            FVar(_) | MVar(_) | Sort(_) | Inductive(_, _)
            | Constructor(_, _, _) | Const(_, _) => {}
            App(f, a) => { f.subst(var_idx, value); a.subst(var_idx, value); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                ty.subst(var_idx, value);
                let mut sv = value.clone(); sv.lift(1, 0);
                body.subst(var_idx + 1, &sv);
            }
            Let(ty, val, body) => {
                ty.subst(var_idx, value);
                val.subst(var_idx, value);
                let mut sv = value.clone(); sv.lift(1, 0);
                body.subst(var_idx + 1, &sv);
            }
            Match(_, target, motive, branches) => {
                target.subst(var_idx, value);
                let mut sv = value.clone(); sv.lift(1, 0);
                motive.subst(var_idx + 1, &sv);
                for b in branches { b.subst(var_idx, value); }
            }
        }
    }

    pub fn subst_levels(&mut self, params: &[(String, Level)]) {
        match self {
            Sort(l) => {
                let mut nl = l.clone();
                for (p, v) in params { nl = nl.subst_param(p, v); }
                *l = nl;
            }
            Const(_, ls) | Inductive(_, ls) | Constructor(_, _, ls) => {
                for l in ls.iter_mut() {
                    for (p, v) in params { *l = l.subst_param(p, v); }
                }
            }
            BVar(_) | FVar(_) | MVar(_) => {}
            App(f, a) => { f.subst_levels(params); a.subst_levels(params); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                ty.subst_levels(params); body.subst_levels(params);
            }
            Let(ty, val, body) => {
                ty.subst_levels(params); val.subst_levels(params); body.subst_levels(params);
            }
            Match(_, target, motive, branches) => {
                target.subst_levels(params); motive.subst_levels(params);
                for b in branches { b.subst_levels(params); }
            }
        }
    }

    pub fn subst_mvar(&mut self, id: usize, value: &Expr) {
        match self {
            MVar(n) => { if *n == id { *self = value.clone(); } }
            BVar(_) | FVar(_) | Sort(_) | Inductive(_, _)
            | Constructor(_, _, _) | Const(_, _) => {}
            App(f, a) => { f.subst_mvar(id, value); a.subst_mvar(id, value); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                ty.subst_mvar(id, value); body.subst_mvar(id, value);
            }
            Let(ty, val, body) => {
                ty.subst_mvar(id, value); val.subst_mvar(id, value); body.subst_mvar(id, value);
            }
            Match(_, target, motive, branches) => {
                target.subst_mvar(id, value); motive.subst_mvar(id, value);
                for b in branches { b.subst_mvar(id, value); }
            }
        }
    }

    pub fn subst_uvar(&mut self, id: &str, val: &Level) {
        match self {
            Sort(l) => { *l = l.subst_uvar(id, val); }
            Const(_, ls) | Inductive(_, ls) | Constructor(_, _, ls) => {
                for l in ls.iter_mut() { *l = l.subst_uvar(id, val); }
            }
            BVar(_) | FVar(_) | MVar(_) => {}
            App(f, a) => { f.subst_uvar(id, val); a.subst_uvar(id, val); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                ty.subst_uvar(id, val); body.subst_uvar(id, val);
            }
            Let(ty, val2, body) => {
                ty.subst_uvar(id, val); val2.subst_uvar(id, val); body.subst_uvar(id, val);
            }
            Match(_, target, motive, branches) => {
                target.subst_uvar(id, val); motive.subst_uvar(id, val);
                for b in branches { b.subst_uvar(id, val); }
            }
        }
    }
}