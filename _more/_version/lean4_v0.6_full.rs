// ============================================================
//  Lean 4 kernel  —  Elaborator + Kernel 雙層架構
//  Layer 0 : Level     (universe level expressions)
//  Layer 1 : Expr      (core calculus, de Bruijn)
//  Layer 2 : Kernel    (definitional equality, type inference)
//  Layer 3 : Elab      (implicit args, universe unification)
//  Layer 4 : Parser    (surface syntax → pre-expressions)
// ============================================================

use std::collections::HashMap;

// ============================================================
// Layer 0 : Universe Levels
// ============================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    UVar(String), // universe metavariable  ?u
    Param(String), // universe parameter     u
}

impl Level {
    pub fn of_nat(n: usize) -> Level {
        (0..n).fold(Level::Zero, |l, _| Level::Succ(Box::new(l)))
    }

    /// Substitute a universe parameter by a level.
    pub fn subst_param(&self, name: &str, val: &Level) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Box::new(l.subst_param(name, val))),
            Level::Max(a, b) => Level::Max(
                Box::new(a.subst_param(name, val)),
                Box::new(b.subst_param(name, val)),
            ),
            Level::IMax(a, b) => Level::IMax(
                Box::new(a.subst_param(name, val)),
                Box::new(b.subst_param(name, val)),
            ),
            Level::UVar(n) => Level::UVar(n.clone()),
            Level::Param(n) => {
                if n == name { val.clone() } else { Level::Param(n.clone()) }
            }
        }
    }

    /// Substitute a universe metavariable.
    pub fn subst_uvar(&self, id: &str, val: &Level) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Box::new(l.subst_uvar(id, val))),
            Level::Max(a, b) => Level::Max(
                Box::new(a.subst_uvar(id, val)),
                Box::new(b.subst_uvar(id, val)),
            ),
            Level::IMax(a, b) => Level::IMax(
                Box::new(a.subst_uvar(id, val)),
                Box::new(b.subst_uvar(id, val)),
            ),
            Level::UVar(n) => {
                if n == id { val.clone() } else { Level::UVar(n.clone()) }
            }
            Level::Param(n) => Level::Param(n.clone()),
        }
    }

    /// Normalise to a canonical form (no Max/IMax with identical sides, etc.)
    pub fn normalize(&self) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Box::new(l.normalize())),
            Level::Max(a, b) => {
                let a = a.normalize();
                let b = b.normalize();
                if a == b { return a; }
                Level::Max(Box::new(a), Box::new(b))
            }
            Level::IMax(a, b) => {
                let b = b.normalize();
                match &b {
                    Level::Zero => Level::Zero,
                    _ => {
                        let a = a.normalize();
                        if a == b { return a; }
                        Level::IMax(Box::new(a), Box::new(b))
                    }
                }
            }
            other => other.clone(),
        }
    }

    /// Compute the concrete numeric value if fully ground (no UVar/Param).
    fn to_nat(&self) -> Option<usize> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(l) => l.to_nat().map(|n| n + 1),
            Level::Max(a, b) => {
                let a = a.to_nat()?; let b = b.to_nat()?;
                Some(a.max(b))
            }
            Level::IMax(a, b) => {
                let b = b.to_nat()?;
                if b == 0 { return Some(0); }
                let a = a.to_nat()?;
                Some(a.max(b))
            }
            _ => None,
        }
    }

    pub fn pretty(&self) -> String {
        match self {
            Level::Zero => "0".into(),
            Level::Succ(l) => {
                if let Some(n) = self.to_nat() { return n.to_string(); }
                format!("({} + 1)", l.pretty())
            }
            Level::Max(a, b) => format!("max {} {}", a.pretty(), b.pretty()),
            Level::IMax(a, b) => format!("imax {} {}", a.pretty(), b.pretty()),
            Level::UVar(n) => format!("?{}", n),
            Level::Param(n) => n.clone(),
        }
    }
}

// ============================================================
// Layer 1 : Core Expressions  (de Bruijn, explicit only)
// ============================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    BVar(usize),
    FVar(usize),                        // free variable (elaboration only)
    MVar(usize),                        // expression metavariable
    Sort(Level),
    Const(String, Vec<Level>),          // constant + universe instances
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
    Default,   // (x : T)
    Implicit,  // {x : T}
    Instance,  // [x : T]
}

use Expr::*;

impl Expr {
    // --------------------------------------------------------
    // Helpers
    // --------------------------------------------------------
    pub fn prop() -> Expr { Sort(Level::Zero) }
    pub fn type0() -> Expr { Sort(Level::Succ(Box::new(Level::Zero))) }

    pub fn mk_arrow(a: Expr, mut b: Expr) -> Expr {
        b.lift(1, 0);
        Pi(BinderInfo::Default, Box::new(a), Box::new(b))
    }

    fn get_app_fn_args(&self) -> (&Expr, Vec<Expr>) {
        let mut curr = self;
        let mut args = Vec::new();
        while let App(f, arg) = curr { args.push(*arg.clone()); curr = f; }
        args.reverse();
        (curr, args)
    }

    // --------------------------------------------------------
    // Lift free de Bruijn indices ≥ threshold by amount
    // --------------------------------------------------------
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

    // --------------------------------------------------------
    // Substitute BVar(var_idx) with value (de Bruijn subst)
    // --------------------------------------------------------
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

    // --------------------------------------------------------
    // Substitute universe level parameters
    // --------------------------------------------------------
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

    // --------------------------------------------------------
    // Substitute MVar(id) with value
    // --------------------------------------------------------
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

    // --------------------------------------------------------
    // Substitute universe metavariables throughout
    // --------------------------------------------------------
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

// ============================================================
// Layer 2 : Kernel  (reduction + definitional equality)
// ============================================================

/// Global environment: inductive types, constructors, definitions.
#[derive(Clone)]
pub struct GlobalEnv {
    /// inductive name → (universe params, type)
    pub inductives: HashMap<String, (Vec<String>, Expr)>,
    /// constructor name → (inductive name, tag, universe params, type)
    pub ctors: HashMap<String, (String, usize, Vec<String>, Expr)>,
    /// definition name → (universe params, type, value)
    pub defs: HashMap<String, (Vec<String>, Expr, Expr)>,
}

impl GlobalEnv {
    pub fn new() -> Self {
        GlobalEnv {
            inductives: HashMap::new(),
            ctors: HashMap::new(),
            defs: HashMap::new(),
        }
    }

    pub fn ctor_tag_of(&self, ind: &str, tag: usize) -> Option<&str> {
        self.ctors.iter()
            .find(|(_, (i, t, _, _))| i == ind && *t == tag)
            .map(|(k, _)| k.as_str())
    }
}

/// Local typing context (stack of types for BVars).
pub struct LocalCtx {
    pub types: Vec<Expr>,
}

impl LocalCtx {
    pub fn new() -> Self { LocalCtx { types: Vec::new() } }
    pub fn push(&mut self, ty: Expr) { self.types.push(ty); }
    pub fn pop(&mut self) { self.types.pop(); }
    pub fn get(&self, n: usize) -> Option<&Expr> {
        let len = self.types.len();
        if n < len { Some(&self.types[len - 1 - n]) } else { None }
    }
}

pub struct Kernel<'e> {
    pub env: &'e GlobalEnv,
}

impl<'e> Kernel<'e> {
    pub fn new(env: &'e GlobalEnv) -> Self { Kernel { env } }

    // --------------------------------------------------------
    // Weak-head normal form
    // --------------------------------------------------------
    pub fn whnf(&self, expr: &mut Expr) {
        let mut next: Option<Expr> = None;
        match expr {
            Const(name, lvls) => {
                if let Some((params, _, val)) = self.env.defs.get(name) {
                    let mut v = val.clone();
                    let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                    v.subst_levels(&substs);
                    next = Some(v);
                }
            }
            Let(_, val, body) => {
                let mut b = *body.clone();
                b.subst(0, val);
                next = Some(b);
            }
            App(f, arg) => {
                self.whnf(f);
                match f.as_mut() {
                    Lam(_, _, body) => {
                        let mut b = *body.clone();
                        b.subst(0, arg);
                        next = Some(b);
                    }
                    Fix(_, body) => {
                        let mut b = *body.clone();
                        b.subst(0, &**f);
                        next = Some(App(Box::new(b), arg.clone()));
                    }
                    _ => {}
                }
            }
            Match(ind_name, target, _motive, branches) => {
                self.whnf(target);
                let (head, args) = target.get_app_fn_args();
                if let Constructor(c_ind, tag, _) = head {
                    if c_ind == ind_name && *tag < branches.len() {
                        let mut res = branches[*tag].clone();
                        for a in args { res = App(Box::new(res), Box::new(a)); }
                        next = Some(res);
                    }
                }
            }
            _ => {}
        }
        if let Some(mut n) = next { self.whnf(&mut n); *expr = n; }
    }

    // --------------------------------------------------------
    // Full normal form
    // --------------------------------------------------------
    pub fn nf(&self, expr: &mut Expr) {
        self.whnf(expr);
        match expr {
            App(f, a) => { self.nf(f); self.nf(a); }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                self.nf(ty); self.nf(body);
            }
            Let(ty, val, body) => { self.nf(ty); self.nf(val); self.nf(body); }
            Match(_, target, motive, branches) => {
                self.nf(target); self.nf(motive);
                for b in branches { self.nf(b); }
            }
            _ => {}
        }
    }

    // --------------------------------------------------------
    // Structural equality after full normalisation
    // --------------------------------------------------------
    fn struct_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (a, b) {
            (BVar(i), BVar(j)) => i == j,
            (FVar(i), FVar(j)) => i == j,
            (MVar(i), MVar(j)) => i == j,
            (Sort(l1), Sort(l2)) => l1.normalize() == l2.normalize(),
            (Const(n1, ls1), Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (Inductive(n1, ls1), Inductive(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (Constructor(n1, t1, ls1), Constructor(n2, t2, ls2)) =>
                n1 == n2 && t1 == t2 && ls1 == ls2,
            (App(f1, a1), App(f2, a2)) =>
                self.struct_eq(f1, f2) && self.struct_eq(a1, a2),
            (Lam(bi1, ty1, b1), Lam(bi2, ty2, b2))
            | (Pi(bi1, ty1, b1), Pi(bi2, ty2, b2)) =>
                bi1 == bi2 && self.struct_eq(ty1, ty2) && self.struct_eq(b1, b2),
            (Fix(ty1, b1), Fix(ty2, b2)) =>
                self.struct_eq(ty1, ty2) && self.struct_eq(b1, b2),
            (Let(ty1, v1, b1), Let(ty2, v2, b2)) =>
                self.struct_eq(ty1, ty2) && self.struct_eq(v1, v2) && self.struct_eq(b1, b2),
            _ => false,
        }
    }

    pub fn def_eq(&self, e1: &Expr, e2: &Expr) -> bool {
        let mut w1 = e1.clone(); self.nf(&mut w1);
        let mut w2 = e2.clone(); self.nf(&mut w2);
        self.struct_eq(&w1, &w2)
    }

    // --------------------------------------------------------
    // Type inference  (kernel, no elaboration)
    // --------------------------------------------------------
    pub fn infer(&self, expr: &Expr, lctx: &mut LocalCtx) -> Result<Expr, String> {
        match expr {
            BVar(n) => {
                let mut ty = lctx.get(*n)
                    .ok_or_else(|| format!("Unbound BVar({})", n))?.clone();
                ty.lift(*n + 1, 0);
                Ok(ty)
            }
            FVar(_) => Err("FVar should not reach kernel".into()),
            MVar(_) => Err("Unsolved metavariable in kernel check".into()),
            Sort(l) => Ok(Sort(Level::Succ(Box::new(l.clone())))),
            Const(name, lvls) => {
                let (params, ty, _) = self.env.defs.get(name)
                    .ok_or_else(|| format!("Unknown constant: {}", name))?;
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            Inductive(name, lvls) => {
                let (params, ty) = self.env.inductives.get(name)
                    .ok_or_else(|| format!("Unknown inductive: {}", name))?;
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            Constructor(ind, tag, lvls) => {
                let ctor_name = self.env.ctor_tag_of(ind, *tag)
                    .ok_or_else(|| format!("Unknown constructor {}.{}", ind, tag))?;
                let (_, _, params, ty) = self.env.ctors.get(ctor_name).unwrap();
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            App(f, arg) => {
                let mut f_ty = self.infer(f, lctx)?;
                self.whnf(&mut f_ty);
                match f_ty {
                    Pi(_, param_ty, ret_ty) => {
                        let arg_ty = self.infer(arg, lctx)?;
                        if !self.def_eq(&arg_ty, &param_ty) {
                            return Err(format!(
                                "App type mismatch:\n  expected: {}\n  got:      {}",
                                pretty_expr(&param_ty, self.env),
                                pretty_expr(&arg_ty, self.env)
                            ));
                        }
                        let mut ret = *ret_ty;
                        ret.subst(0, arg);
                        Ok(ret)
                    }
                    _ => Err(format!("Expected Pi, got: {}", pretty_expr(&f_ty, self.env))),
                }
            }
            Lam(bi, ty, body) => {
                self.infer(ty, lctx)?;
                lctx.push(*ty.clone());
                let body_ty = self.infer(body, lctx)?;
                lctx.pop();
                Ok(Pi(bi.clone(), ty.clone(), Box::new(body_ty)))
            }
            Pi(_, ty, body) => {
                let s1 = self.infer(ty, lctx)?;
                lctx.push(*ty.clone());
                let s2 = self.infer(body, lctx)?;
                lctx.pop();
                // universe of Pi is imax(u, v)
                let l1 = sort_level(s1).ok_or("Pi domain not a Sort")?;
                let l2 = sort_level(s2).ok_or("Pi codomain not a Sort")?;
                let l = Level::IMax(Box::new(l1), Box::new(l2)).normalize();
                Ok(Sort(l))
            }
            Let(ty, val, body) => {
                let val_ty = self.infer(val, lctx)?;
                if !self.def_eq(&val_ty, ty) {
                    return Err("Let type mismatch".into());
                }
                lctx.push(*ty.clone());
                let mut body_ty = self.infer(body, lctx)?;
                lctx.pop();
                body_ty.subst(0, val);
                Ok(body_ty)
            }
            Fix(ty, body) => {
                lctx.push(*ty.clone());
                let body_ty = self.infer(body, lctx)?;
                lctx.pop();
                let fix_expr = Fix(ty.clone(), body.clone());
                let mut closed = body_ty;
                closed.subst(0, &fix_expr);
                if !self.def_eq(&closed, ty) {
                    return Err("Fixpoint type mismatch".into());
                }
                Ok(*ty.clone())
            }
            Match(_, target, motive, _) => {
                let mut motive_whnf = *motive.clone();
                self.whnf(&mut motive_whnf);
                match motive_whnf {
                    Lam(_, _, _) => {
                        let mut result_ty = App(motive.clone(), target.clone());
                        self.whnf(&mut result_ty);
                        Ok(result_ty)
                    }
                    _ => Ok(*motive.clone()),
                }
            }
        }
    }
}

fn sort_level(e: Expr) -> Option<Level> {
    if let Sort(l) = e { Some(l) } else { None }
}

// ============================================================
// Layer 3 : Elaborator
// ============================================================

/// Pre-expression: surface-level, may have implicit binders,
/// named variables, and holes `_`.
#[derive(Debug, Clone)]
pub enum PreExpr {
    Var(String),
    Hole,                                              // _
    NatLit(usize),
    Sort(PreLevel),
    App(Box<PreExpr>, Box<PreExpr>),
    Lam(BinderInfo, String, Box<PreExpr>, Box<PreExpr>),
    Pi(BinderInfo, String, Box<PreExpr>, Box<PreExpr>),
    Let(String, Box<PreExpr>, Box<PreExpr>, Box<PreExpr>),
    Fix(String, Box<PreExpr>, Box<PreExpr>),
    Match(String, Box<PreExpr>, Option<Box<PreExpr>>, Vec<(String, Vec<String>, Box<PreExpr>)>),
}

#[derive(Debug, Clone)]
pub enum PreLevel {
    Nat(usize),
    Param(String),
    Succ(Box<PreLevel>),
    Max(Box<PreLevel>, Box<PreLevel>),
    IMax(Box<PreLevel>, Box<PreLevel>),
}

impl PreLevel {
    fn to_level(&self, uparams: &[String]) -> Level {
        match self {
            PreLevel::Nat(n) => Level::of_nat(*n),
            PreLevel::Param(s) => {
                if uparams.contains(s) { Level::Param(s.clone()) }
                else { panic!("Unknown universe parameter: {}", s) }
            }
            PreLevel::Succ(l) => Level::Succ(Box::new(l.to_level(uparams))),
            PreLevel::Max(a, b) =>
                Level::Max(Box::new(a.to_level(uparams)), Box::new(b.to_level(uparams))),
            PreLevel::IMax(a, b) =>
                Level::IMax(Box::new(a.to_level(uparams)), Box::new(b.to_level(uparams))),
        }
    }
}

pub struct Elaborator {
    pub env: GlobalEnv,
    // metavariable solutions
    mvar_types: Vec<Expr>,          // MVar(i) has type mvar_types[i]
    mvar_sols: Vec<Option<Expr>>,   // MVar(i) solved to mvar_sols[i]
    // universe metavariable solutions
    uvar_count: usize,
    uvar_sols: HashMap<String, Level>,
    // local free variable context for elaboration
    fvar_types: Vec<Expr>,          // FVar(i) : fvar_types[i]
    fvar_names: Vec<String>,
    fvar_depth: Vec<usize>,           // FVar(i) was introduced at binder depth fvar_depth[i]
    current_depth: usize,             // current binder nesting depth
    // local name → FVar index  (top of stack = most recent)
    name_env: Vec<(String, usize)>,
}

impl Elaborator {
    pub fn new() -> Self {
        Elaborator {
            env: GlobalEnv::new(),
            mvar_types: Vec::new(),
            mvar_sols: Vec::new(),
            uvar_count: 0,
            uvar_sols: HashMap::new(),
            fvar_types: Vec::new(),
            fvar_names: Vec::new(),
            fvar_depth: Vec::new(),
            current_depth: 0,
            name_env: Vec::new(),
        }
    }

    // ---- metavariable management --------------------------------

    fn fresh_mvar(&mut self, ty: Expr) -> Expr {
        let id = self.mvar_types.len();
        self.mvar_types.push(ty);
        self.mvar_sols.push(None);
        MVar(id)
    }

    fn fresh_uvar(&mut self) -> Level {
        let name = format!("u{}", self.uvar_count);
        self.uvar_count += 1;
        Level::UVar(name)
    }

    fn apply_mvar_sols(&self, expr: &mut Expr) {
        for (i, sol) in self.mvar_sols.iter().enumerate() {
            if let Some(v) = sol {
                expr.subst_mvar(i, v);
            }
        }
        // Apply universe metavar solutions too
        for (k, v) in &self.uvar_sols {
            expr.subst_uvar(k, v);
        }
    }

    fn solve_mvar(&mut self, id: usize, val: Expr) -> Result<(), String> {
        if self.mvar_sols[id].is_some() {
            let existing = self.mvar_sols[id].clone().unwrap();
            let k = Kernel::new(&self.env);
            if !k.def_eq(&existing, &val) {
                return Err(format!("Metavariable ?{} solved twice with incompatible values", id));
            }
            return Ok(());
        }
        self.mvar_sols[id] = Some(val);
        Ok(())
    }

    // ---- free variable management --------------------------------

    fn push_fvar(&mut self, name: String, ty: Expr) -> usize {
        let id = self.fvar_types.len();
        self.fvar_types.push(ty);
        self.fvar_names.push(name.clone());
        self.fvar_depth.push(self.current_depth);
        self.name_env.push((name, id));
        self.current_depth += 1;
        id
    }

    fn pop_fvar(&mut self) {
        self.name_env.pop();
        self.current_depth -= 1;
        // Note: fvar_types stays (monotone), only name_env pops
    }

    fn lookup_name(&self, name: &str) -> Option<usize> {
        self.name_env.iter().rev()
            .find(|(n, _)| n == name)
            .map(|(_, id)| *id)
    }

    // ---- universe unification ------------------------------------

    fn unify_level(&mut self, l1: &Level, l2: &Level) -> Result<(), String> {
        let l1n = l1.normalize();
        let l2n = l2.normalize();
        if l1n == l2n { return Ok(()); }
        match (&l1n, &l2n) {
            (Level::UVar(n), other) | (other, Level::UVar(n)) => {
                let n = n.clone();
                let other = other.clone();
                if let Some(existing) = self.uvar_sols.get(&n).cloned() {
                    return self.unify_level(&existing, &other);
                }
                self.uvar_sols.insert(n.clone(), other.clone());
                // propagate to all expressions? Done lazily via apply_mvar_sols
                Ok(())
            }
            _ => Err(format!("Universe mismatch: {} vs {}", l1n.pretty(), l2n.pretty())),
        }
    }

    // ---- expression unification (for implicit arg solving) ------

    fn unify(&mut self, e1: &Expr, e2: &Expr) -> Result<(), String> {
        let mut a = e1.clone(); self.apply_mvar_sols(&mut a);
        let mut b = e2.clone(); self.apply_mvar_sols(&mut b);

        // Apply env for reduction
        let k = Kernel::new(&self.env);
        k.whnf(&mut a); k.whnf(&mut b);

        match (&a.clone(), &b.clone()) {
            (MVar(i), _) => self.solve_mvar(*i, b),
            (_, MVar(i)) => self.solve_mvar(*i, a),
            (Sort(l1), Sort(l2)) => self.unify_level(l1, l2),
            (BVar(i), BVar(j)) if i == j => Ok(()),
            (FVar(i), FVar(j)) if i == j => Ok(()),
            (Inductive(n1, ls1), Inductive(n2, ls2)) if n1 == n2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (Constructor(n1, t1, ls1), Constructor(n2, t2, ls2)) if n1 == n2 && t1 == t2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (Const(n1, ls1), Const(n2, ls2)) if n1 == n2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (App(f1, a1), App(f2, a2)) => {
                self.unify(f1, f2)?; self.unify(a1, a2)
            }
            (Lam(_, ty1, b1), Lam(_, ty2, b2))
            | (Pi(_, ty1, b1), Pi(_, ty2, b2)) => {
                self.unify(ty1, ty2)?; self.unify(b1, b2)
            }
            _ => {
                // Last resort: full normalisation + structural eq
                let mut na = a.clone(); k.nf(&mut na);
                let mut nb = b.clone(); k.nf(&mut nb);
                if k.struct_eq(&na, &nb) { Ok(()) }
                else { Err(format!(
                    "Cannot unify:\n  {}\n  {}",
                    pretty_expr(&na, &self.env),
                    pretty_expr(&nb, &self.env)
                ))}
            }
        }
    }

    // ---- convert FVar-based expr back to de Bruijn BVar --------
    // (used when finishing elaboration of a binder body)
    fn fvar_to_bvar(&self, expr: &mut Expr, fvar_id: usize, depth: usize) {
        match expr {
            FVar(id) => { if *id == fvar_id { *expr = BVar(depth); } }
            BVar(_) | MVar(_) | Sort(_) | Inductive(_, _)
            | Constructor(_, _, _) | Const(_, _) => {}
            App(f, a) => {
                self.fvar_to_bvar(f, fvar_id, depth);
                self.fvar_to_bvar(a, fvar_id, depth);
            }
            Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
                self.fvar_to_bvar(ty, fvar_id, depth);
                self.fvar_to_bvar(body, fvar_id, depth + 1);
            }
            Let(ty, val, body) => {
                self.fvar_to_bvar(ty, fvar_id, depth);
                self.fvar_to_bvar(val, fvar_id, depth);
                self.fvar_to_bvar(body, fvar_id, depth + 1);
            }
            Match(_, target, motive, branches) => {
                self.fvar_to_bvar(target, fvar_id, depth);
                self.fvar_to_bvar(motive, fvar_id, depth + 1);
                for b in branches { self.fvar_to_bvar(b, fvar_id, depth); }
            }
        }
    }

    // ---- build a LocalCtx from the current FVar stack ----------
    fn build_lctx(&self) -> LocalCtx {
        // For each FVar referenced in name_env in order,
        // the types form the local context.
        // Since kernel uses BVar, we use a simple stack.
        let mut lctx = LocalCtx::new();
        // name_env is ordered oldest→newest; we push oldest first
        for (_, id) in &self.name_env {
            lctx.push(self.fvar_types[*id].clone());
        }
        lctx
    }

    // ---- main elaboration entry point ---------------------------

    pub fn elab(&mut self, pre: &PreExpr, expected_ty: Option<&Expr>,
                uparams: &[String]) -> Result<Expr, String> {
        match pre {
            PreExpr::Hole => {
                let ty = expected_ty.cloned().unwrap_or_else(|| {
                    let u = self.fresh_uvar();
                    Sort(u)
                });
                Ok(self.fresh_mvar(ty))
            }

            PreExpr::NatLit(n) => {
                let zero = Constructor("Nat".into(), 0, vec![]);
                Ok((0..*n).fold(zero, |acc, _| {
                    App(Box::new(Constructor("Nat".into(), 1, vec![])), Box::new(acc))
                }))
            }

            PreExpr::Sort(pl) => {
                let l = pl.to_level(uparams);
                Ok(Sort(l))
            }

            PreExpr::Var(name) => {
                // 1. Local free variable?
                if let Some(fvar_id) = self.lookup_name(name) {
                    return Ok(FVar(fvar_id));
                }
                // 2. Constructor?
                if let Some((ind, tag, params, _)) = self.env.ctors.get(name) {
                    let ind = ind.clone(); let tag = *tag;
                    let n_params = params.len();
                    let lvls: Vec<Level> = (0..n_params).map(|_| self.fresh_uvar()).collect();
                    return Ok(Constructor(ind, tag, lvls));
                }
                // 3. Inductive?
                if let Some((params, _)) = self.env.inductives.get(name) {
                    let n_params = params.len();
                    let name = name.clone();
                    let lvls: Vec<Level> = (0..n_params).map(|_| self.fresh_uvar()).collect();
                    return Ok(Inductive(name, lvls));
                }
                // 4. Definition?
                if let Some((params, _, _)) = self.env.defs.get(name) {
                    let n_params = params.len();
                    let name = name.clone();
                    let lvls: Vec<Level> = (0..n_params).map(|_| self.fresh_uvar()).collect();
                    return Ok(Const(name, lvls));
                }
                Err(format!("Unknown identifier: {}", name))
            }

            PreExpr::Lam(bi, param_name, param_ty_pre, body_pre) => {
                let param_ty = self.elab(param_ty_pre, None, uparams)?;
                let _fvar_id = self.push_fvar(param_name.clone(), param_ty.clone());
                let body_exp = expected_ty.and_then(|ty| {
                    let mut w = ty.clone();
                    Kernel::new(&self.env).whnf(&mut w);
                    if let Pi(_, _, ret) = w { Some(*ret) } else { None }
                });
                let body = self.elab(body_pre, body_exp.as_ref(), uparams)?;
                self.pop_fvar();
                // FVar(fvar_id) stays in body/param_ty; converted at top by fvars_to_bvars
                Ok(Lam(bi.clone(), Box::new(param_ty), Box::new(body)))
            }

            PreExpr::Pi(bi, param_name, param_ty_pre, body_pre) => {
                let param_ty = self.elab(param_ty_pre, None, uparams)?;
                let _fvar_id = self.push_fvar(param_name.clone(), param_ty.clone());
                let body = self.elab(body_pre, None, uparams)?;
                self.pop_fvar();
                Ok(Pi(bi.clone(), Box::new(param_ty), Box::new(body)))
            }

            PreExpr::Let(name, ty_pre, val_pre, body_pre) => {
                let ty = self.elab(ty_pre, None, uparams)?;
                let val = self.elab(val_pre, Some(&ty), uparams)?;
                let _fvar_id = self.push_fvar(name.clone(), ty.clone());
                let body = self.elab(body_pre, expected_ty, uparams)?;
                self.pop_fvar();
                Ok(Let(Box::new(ty), Box::new(val), Box::new(body)))
            }

            PreExpr::Fix(fname, ty_pre, body_pre) => {
                let ty = self.elab(ty_pre, None, uparams)?;
                let _fvar_id = self.push_fvar(fname.clone(), ty.clone());
                let body = self.elab(body_pre, Some(&ty), uparams)?;
                self.pop_fvar();
                Ok(Fix(Box::new(ty), Box::new(body)))
            }

            PreExpr::App(f_pre, arg_pre) => {
                let f = self.elab(f_pre, None, uparams)?;
                // Infer type of f to check for implicit leading arguments
                let f_with_implicits = self.insert_implicits(f, uparams).map_err(|e| format!("insert_implicits: {}", e))?;
                let (f_expr, f_ty) = f_with_implicits;
                let mut f_ty_whnf = f_ty.clone();
                let k = Kernel::new(&self.env);
                k.whnf(&mut f_ty_whnf);
                let arg_exp_ty = if let Pi(_, param_ty, _) = &f_ty_whnf {
                    Some(*param_ty.clone())
                } else { None };
                let arg = self.elab(arg_pre, arg_exp_ty.as_ref(), uparams)?;
                // Unify arg type with expected
                if let Pi(_, param_ty, _) = &f_ty_whnf {
                    let arg_ty = {
                        let mut lctx = self.build_lctx();
                        // convert FVars in arg to BVars for kernel
                        let mut arg_k = arg.clone();
                        self.fvars_to_bvars(&mut arg_k);
                        Kernel::new(&self.env).infer(&arg_k, &mut lctx)?
                    };
                    self.unify(&arg_ty, param_ty)?;
                }
                Ok(App(Box::new(f_expr), Box::new(arg)))
            }

            PreExpr::Match(ind_name, target_pre, motive_pre, branches_pre) => {
                let target = self.elab(target_pre, None, uparams)?;

                // Elaborate motive: either explicit or infer from branches
                let motive: Expr = if let Some(m_pre) = motive_pre {
                    self.elab(m_pre, None, uparams)?
                } else {
                    // Default: motive is fun _ => ?T  (non-dependent)
                    let u = self.fresh_uvar();
                    let ret_ty = self.fresh_mvar(Sort(u));
                    let mut lam_body = ret_ty;
                    lam_body.lift(1, 0);
                    // Get inductive type for the motive parameter
                    let ind_ty = self.env.inductives.get(ind_name)
                        .map(|(_, t)| t.clone())
                        .unwrap_or(Sort(Level::Zero));
                    Lam(BinderInfo::Default, Box::new(ind_ty), Box::new(lam_body))
                };

                let mut branches: Vec<Expr> = Vec::new();
                // motive_ret_mvar: if motive is auto Lam(_,?T), record MVar id to unify later
                let motive_ret_mvar: Option<usize> = match &motive {
                    Lam(_, _, body) => if let MVar(id) = body.as_ref() { Some(*id) } else { None },
                    _ => None,
                };
                // If we know the expected return type, solve the motive MVar immediately
                if let (Some(mv_id), Some(exp_ty)) = (motive_ret_mvar, expected_ty) {
                    if self.mvar_sols[mv_id].is_none() {
                        let _ = self.solve_mvar(mv_id, exp_ty.clone());
                    }
                }
                for (ctor_name, binder_names, branch_body_pre) in branches_pre {
                    let (_, _, _, ctor_ty) = self.env.ctors.get(ctor_name)
                        .ok_or_else(|| format!("Unknown constructor: {}", ctor_name))?.clone();

                    // Push binders for constructor arguments
                    let mut fvar_ids = Vec::new();
                    let mut cur_ty = ctor_ty.clone();
                    for bname in binder_names {
                        let mut cty = cur_ty.clone();
                        Kernel::new(&self.env).whnf(&mut cty);
                        if let Pi(_, param_ty, ret) = cty {
                            let fid = self.push_fvar(bname.clone(), *param_ty);
                            fvar_ids.push(fid);
                            cur_ty = *ret;
                        } else {
                            return Err(format!(
                                "Too many binders for constructor {}", ctor_name));
                        }
                    }
                    let branch_body = self.elab(branch_body_pre, None, uparams)?;

                    // Unify branch body type with motive return type
                    if let Some(mv_id) = motive_ret_mvar {
                        if self.mvar_sols[mv_id].is_none() {
                            // Build lctx with the branch binders
                            let mut lctx = LocalCtx::new();
                            for fid in &fvar_ids {
                                lctx.push(self.fvar_types[*fid].clone());
                            }
                            let mut bb_k = branch_body.clone();
                            fvars_to_bvars_with_depth(&mut bb_k, &self.fvar_depth, self.current_depth);
                            if let Ok(bb_ty) = Kernel::new(&self.env).infer(&bb_k, &mut lctx) {
                                let _ = self.solve_mvar(mv_id, bb_ty);
                            }
                        }
                    }

                    // Pop binders (new approach: FVars stay, converted globally later)
                    for _ in &fvar_ids { self.pop_fvar(); }
                    // Wrap in lambdas for each binder
                    let mut wrapped = branch_body;
                    for fid in fvar_ids.iter().rev() {
                        let bty = self.fvar_types[*fid].clone();
                        wrapped = Lam(BinderInfo::Default, Box::new(bty), Box::new(wrapped));
                    }
                    branches.push(wrapped);
                }

                // Fill missing branches with mvars
                let n_ctors = self.env.ctors.values()
                    .filter(|(i, _, _, _)| i == ind_name).count();
                while branches.len() < n_ctors {
                    let mv = self.fresh_mvar(Sort(Level::Zero));
                    branches.push(mv);
                }

                Ok(Match(ind_name.clone(), Box::new(target), Box::new(motive), branches))
            }
        }
    }

    /// After elaborating a function, insert implicit arguments as fresh mvars.
    fn insert_implicits(&mut self, f: Expr, uparams: &[String])
        -> Result<(Expr, Expr), String>
    {
        // We need the type of f
        let mut f_k = f.clone();
        self.fvars_to_bvars(&mut f_k);
        let mut lctx = self.build_lctx();
        let f_ty = Kernel::new(&self.env).infer(&f_k, &mut lctx)?;
        let mut result = f;
        let mut result_ty = f_ty;
        loop {
            let mut w = result_ty.clone();
            Kernel::new(&self.env).whnf(&mut w);
            if let Pi(BinderInfo::Implicit, param_ty, ret_ty) = w {
                let mv = self.fresh_mvar(*param_ty);
                result_ty = { let mut r = *ret_ty; r.subst(0, &mv); r };
                result = App(Box::new(result), Box::new(mv));
            } else if let Pi(BinderInfo::Instance, param_ty, ret_ty) = w {
                let mv = self.fresh_mvar(*param_ty);
                result_ty = { let mut r = *ret_ty; r.subst(0, &mv); r };
                result = App(Box::new(result), Box::new(mv));
            } else {
                break;
            }
        }
        Ok((result, result_ty))
    }

    /// Convert all FVars to BVars.
    /// FVar(id) introduced at depth D, at expression position depth P → BVar(P - D - 1)
    fn fvars_to_bvars(&self, expr: &mut Expr) {
        fvars_to_bvars_with_depth(expr, &self.fvar_depth, self.current_depth);
    }

    // ---- elaborate a top-level definition -----------------------

    pub fn elab_def(&mut self, name: &str, uparams: &[String],
                    ty_pre: &PreExpr, val_pre: &PreExpr) -> Result<(), String> {
        // Save depth baseline — FVars introduced during this def start at current depth
        let base_fvar_id = self.fvar_types.len();
        let base_depth = self.current_depth;

        let ty = self.elab(ty_pre, None, uparams)?;
        let mut ty_k = ty.clone();
        self.apply_mvar_sols(&mut ty_k);

        let val = self.elab(val_pre, Some(&ty_k), uparams)?;
        let mut val_k = val.clone();
        // Apply mvar solutions to fixpoint (may need multiple passes)
        for _ in 0..16 {
            let before = format!("{:?}", val_k);
            self.apply_mvar_sols(&mut val_k);
            self.apply_mvar_sols(&mut ty_k);
            if format!("{:?}", val_k) == before { break; }
        }
        // Convert FVars to BVars
        fvars_to_bvars_with_depth(&mut val_k, &self.fvar_depth, self.current_depth);
        fvars_to_bvars_with_depth(&mut ty_k, &self.fvar_depth, self.current_depth);

        let mut lctx = LocalCtx::new();
        Kernel::new(&self.env).infer(&val_k, &mut lctx)?;

        self.env.defs.insert(name.to_string(), (uparams.to_vec(), ty_k, val_k));
        Ok(())
    }
}

/// fvar_depth[id] = the binder depth when FVar(id) was introduced.
/// current_depth = how many binders deep we currently are.
/// BVar index = current_depth - fvar_depth[id] - 1
fn fvars_to_bvars_with_depth(expr: &mut Expr, fvar_depth: &[usize], current_depth: usize) {
    match expr {
        FVar(id) => {
            if *id < fvar_depth.len() {
                let intro_depth = fvar_depth[*id];
                if current_depth > intro_depth {
                    *expr = BVar(current_depth - intro_depth - 1);
                }
            }
        }
        BVar(_) | MVar(_) | Sort(_) | Inductive(_, _)
        | Constructor(_, _, _) | Const(_, _) => {}
        App(f, a) => {
            fvars_to_bvars_with_depth(f, fvar_depth, current_depth);
            fvars_to_bvars_with_depth(a, fvar_depth, current_depth);
        }
        Lam(_, ty, body) | Pi(_, ty, body) | Fix(ty, body) => {
            fvars_to_bvars_with_depth(ty, fvar_depth, current_depth);
            fvars_to_bvars_with_depth(body, fvar_depth, current_depth + 1);
        }
        Let(ty, val, body) => {
            fvars_to_bvars_with_depth(ty, fvar_depth, current_depth);
            fvars_to_bvars_with_depth(val, fvar_depth, current_depth);
            fvars_to_bvars_with_depth(body, fvar_depth, current_depth + 1);
        }
        Match(_, target, motive, branches) => {
            fvars_to_bvars_with_depth(target, fvar_depth, current_depth);
            fvars_to_bvars_with_depth(motive, fvar_depth, current_depth + 1);
            for b in branches { fvars_to_bvars_with_depth(b, fvar_depth, current_depth); }
        }
    }
}

// ============================================================
// Pretty Printer
// ============================================================

fn try_to_nat(expr: &Expr) -> Option<usize> {
    match expr {
        Constructor(ind, 0, _) if ind == "Nat" => Some(0),
        App(f, arg) => {
            if let Constructor(ind, 1, _) = f.as_ref() {
                if ind == "Nat" { return try_to_nat(arg).map(|n| n + 1); }
            }
            None
        }
        _ => None,
    }
}

fn needs_parens(expr: &Expr) -> bool {
    matches!(expr, App(_, _) | Lam(_, _, _) | Pi(_, _, _) | Fix(_, _) | Let(_, _, _))
}

pub fn pretty_expr(expr: &Expr, env: &GlobalEnv) -> String {
    if let Some(n) = try_to_nat(expr) { return n.to_string(); }
    match expr {
        BVar(n) => format!("#{}", n),
        FVar(n) => format!("fv{}", n),
        MVar(n) => format!("?m{}", n),
        Sort(l) => match l.to_nat() {
            Some(0) => "Prop".into(),
            Some(1) => "Type".into(),
            Some(n) => format!("Type {}", n - 1),
            None => format!("Sort ({})", l.pretty()),
        },
        Const(name, lvls) => {
            if lvls.is_empty() { name.clone() }
            else { format!("{}.{{{}}}",name, lvls.iter().map(|l|l.pretty()).collect::<Vec<_>>().join(",")) }
        }
        Inductive(name, _) => name.clone(),
        Constructor(ind, tag, _) => {
            env.ctor_tag_of(ind, *tag).map(|s| s.to_string())
                .unwrap_or_else(|| format!("{}.ctor{}", ind, tag))
        }
        App(f, arg) => {
            let arg_s = pretty_expr(arg, env);
            let arg_f = if needs_parens(arg) { format!("({})", arg_s) } else { arg_s };
            format!("{} {}", pretty_expr(f, env), arg_f)
        }
        Lam(bi, ty, body) => {
            let bi_s = match bi { BinderInfo::Implicit => "{" , BinderInfo::Instance => "[", _ => "(" };
            let bi_e = match bi { BinderInfo::Implicit => "}" , BinderInfo::Instance => "]", _ => ")" };
            format!("fun {}_ : {}{} => {}", bi_s, pretty_expr(ty, env), bi_e, pretty_expr(body, env))
        }
        Pi(bi, ty, body) => {
            match bi {
                BinderInfo::Default => format!("{} → {}", pretty_expr(ty, env), pretty_expr(body, env)),
                BinderInfo::Implicit => format!("{{_ : {}}} → {}", pretty_expr(ty, env), pretty_expr(body, env)),
                BinderInfo::Instance => format!("[_ : {}] → {}", pretty_expr(ty, env), pretty_expr(body, env)),
            }
        }
        Fix(ty, body) => format!("fix _ : {} => {}", pretty_expr(ty, env), pretty_expr(body, env)),
        Let(ty, val, body) => format!("let _ : {} := {}; {}", pretty_expr(ty,env), pretty_expr(val,env), pretty_expr(body,env)),
        Match(ind, target, motive, branches) => {
            let bs: Vec<String> = branches.iter().enumerate().map(|(i, b)| {
                let cname = env.ctor_tag_of(ind, i).unwrap_or("_");
                format!("| {} => {}", cname, pretty_expr(b, env))
            }).collect();
            format!("match {} return {} with {}", pretty_expr(target,env), pretty_expr(motive,env), bs.join(" "))
        }
    }
}

// ============================================================
// Layer 4 : Parser  (surface syntax → PreExpr)
// ============================================================

struct Parser { tokens: Vec<String>, pos: usize }

impl Parser {
    fn peek(&self) -> Option<&str> { self.tokens.get(self.pos).map(|s| s.as_str()) }
    fn next_tok(&mut self) -> String {
        let t = self.tokens[self.pos].clone(); self.pos += 1; t
    }
    fn consume(&mut self, expected: &str) {
        let t = self.next_tok();
        if t != expected { panic!("Expected '{}', got '{}'", expected, t); }
    }
    fn eof(&self) -> bool { self.pos >= self.tokens.len() }
    fn at(&self, s: &str) -> bool { self.peek() == Some(s) }
}

fn is_terminator(t: &str) -> bool {
    matches!(t, ")" | "}" | "]" | "->" | "→" | "=>" | ":=" | ";" | "|"
        | "," | "with" | "return" | "where" | "def" | "inductive"
        | "#eval" | "#check" | "universe")
}

fn tokenize(src: &str) -> Vec<String> {
    // Remove comments
    let cleaned = src.lines()
        .map(|line| if let Some(i) = line.find("--") { &line[..i] } else { line })
        .collect::<Vec<_>>().join(" ");

    // Insert spaces around all punctuation EXCEPT := (keep together)
    let mut out = String::new();
    let chars: Vec<char> = cleaned.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        // Handle :=  →  as two-char tokens
        if i + 1 < chars.len() && chars[i] == ':' && chars[i+1] == '=' {
            out.push_str(" := "); i += 2; continue;
        }
        if i + 1 < chars.len() && chars[i] == '-' && chars[i+1] == '>' {
            out.push_str(" -> "); i += 2; continue;
        }
        match chars[i] {
            '(' | ')' | '{' | '}' | '[' | ']' | ':' | ';' | ',' | '|' | '→' => {
                out.push(' '); out.push(chars[i]); out.push(' ');
            }
            c => out.push(c),
        }
        i += 1;
    }
    out.split_whitespace().map(|s| s.to_string()).collect()
}

// Parse a universe level expression
fn parse_level(p: &mut Parser) -> PreLevel {
    let tok = p.next_tok();
    match tok.as_str() {
        "max" => {
            let a = parse_level(p); let b = parse_level(p);
            PreLevel::Max(Box::new(a), Box::new(b))
        }
        "imax" => {
            let a = parse_level(p); let b = parse_level(p);
            PreLevel::IMax(Box::new(a), Box::new(b))
        }
        s => {
            if let Ok(n) = s.parse::<usize>() { PreLevel::Nat(n) }
            else { PreLevel::Param(s.to_string()) }
        }
    }
}

fn parse_atom(p: &mut Parser) -> PreExpr {
    let tok = p.next_tok();
    match tok.as_str() {
        "_" => PreExpr::Hole,
        "(" => {
            let e = parse_expr(p);
            p.consume(")");
            e
        }
        "Prop" => PreExpr::Sort(PreLevel::Nat(0)),
        "Type" => {
            // Type or Type N or Type u
            if !p.eof() && !is_terminator(p.peek().unwrap_or("")) {
                let l = parse_level(p);
                PreExpr::Sort(PreLevel::Succ(Box::new(l)))
            } else {
                PreExpr::Sort(PreLevel::Nat(1))
            }
        }
        "Sort" => {
            let l = parse_level(p);
            PreExpr::Sort(l)
        }
        s => {
            if let Ok(n) = s.parse::<usize>() {
                return PreExpr::NatLit(n);
            }
            PreExpr::Var(s.to_string())
        }
    }
}

fn parse_app(p: &mut Parser) -> PreExpr {
    let mut res = parse_atom(p);
    while !p.eof() && !is_terminator(p.peek().unwrap()) {
        res = PreExpr::App(Box::new(res), Box::new(parse_atom(p)));
    }
    res
}

// Parse a binder: (x : T) or {x : T} or [x : T]
// Returns (binder_info, name, type_pre) if successful, else restores pos
fn try_parse_binder(p: &mut Parser) -> Option<(BinderInfo, String, PreExpr)> {
    let (bi, open, close) = match p.peek()? {
        "(" => (BinderInfo::Default, "(", ")"),
        "{" => (BinderInfo::Implicit, "{", "}"),
        "[" => (BinderInfo::Instance, "[", "]"),
        _ => return None,
    };
    let saved = p.pos;
    p.pos += 1;
    // peek for  ident :
    let maybe_name = p.peek().map(|s| s.to_string());
    if let Some(name) = maybe_name {
        let is_ident = !is_terminator(&name) && name != "(" && name != "{" && name != "[";
        if is_ident {
            p.pos += 1;
            if p.at(":") {
                p.consume(":");
                let ty = parse_expr(p);
                if p.at(close) {
                    p.pos += 1;
                    return Some((bi, name, ty));
                }
            }
        }
    }
    p.pos = saved;
    None
}

fn parse_arrow(p: &mut Parser) -> PreExpr {
    // Named Pi binder?
    if let Some((bi, name, ty)) = try_parse_binder(p) {
        if p.at("->") || p.at("→") {
            p.pos += 1;
            let body = parse_arrow(p);
            return PreExpr::Pi(bi, name, Box::new(ty), Box::new(body));
        }
        // Not an arrow — it was a parenthesised expression; re-parse
        // (This shouldn't happen in practice since binders always precede ->)
        // Fall through by treating as App head
        // Reconstruct as App of the binder expression... tricky.
        // Simplest: just return what we have as an expr.
        return ty; // fallback (handles edge cases)
    }

    let mut res = parse_app(p);
    while p.peek() == Some("->") || p.peek() == Some("→") {
        p.pos += 1;
        let right = parse_arrow(p);
        res = PreExpr::Pi(BinderInfo::Default, "_".into(), Box::new(res), Box::new(right));
    }
    res
}

fn parse_expr(p: &mut Parser) -> PreExpr {
    match p.peek() {
        Some("fun") => {
            p.consume("fun");
            // Parse binders until =>
            let mut binders: Vec<(BinderInfo, String, PreExpr)> = Vec::new();
            while !p.at("=>") {
                if let Some(b) = try_parse_binder(p) {
                    binders.push(b);
                } else {
                    panic!("Expected binder in fun, got {:?}", p.peek());
                }
            }
            p.consume("=>");
            let body = parse_expr(p);
            // Fold right: fun (x:A) (y:B) => e  ↦  Lam x A (Lam y B e)
            binders.into_iter().rev().fold(body, |acc, (bi, name, ty)| {
                PreExpr::Lam(bi, name, Box::new(ty), Box::new(acc))
            })
        }
        Some("fix") => {
            p.consume("fix");
            let fname = p.next_tok();
            p.consume(":");
            let ty = parse_expr(p);
            p.consume("=>");
            let body = parse_expr(p);
            PreExpr::Fix(fname, Box::new(ty), Box::new(body))
        }
        Some("let") => {
            p.consume("let");
            let name = p.next_tok();
            p.consume(":");
            let ty = parse_expr(p);
            p.consume(":=");
            let val = parse_expr(p);
            p.consume(";");
            let body = parse_expr(p);
            PreExpr::Let(name, Box::new(ty), Box::new(val), Box::new(body))
        }
        Some("match") => {
            p.consume("match");
            let target = parse_expr(p);
            // optional "return <motive>"
            let motive = if p.at("return") {
                p.consume("return");
                Some(Box::new(parse_expr(p)))
            } else { None };
            p.consume("with");
            let mut branches = Vec::new();
            while !p.eof() && p.at("|") {
                p.consume("|");
                // constructor pattern: Ctor binder*
                let ctor_name = p.next_tok();
                let mut binder_names = Vec::new();
                while !p.at("=>") {
                    binder_names.push(p.next_tok());
                }
                p.consume("=>");
                let body = parse_expr(p);
                branches.push((ctor_name, binder_names, Box::new(body)));
            }
            // Extract inductive name from first branch's constructor
            let ind_name = if !branches.is_empty() {
                branches[0].0.split('.').next().unwrap_or("").to_string()
            } else { "".to_string() };
            PreExpr::Match(ind_name, Box::new(target), motive, branches)
        }
        _ => parse_arrow(p),
    }
}

// ============================================================
// Top-level script runner
// ============================================================


// Parse  name  or  name.{u v w}  into (name, uparams)
fn parse_name_uparams(raw: String, p: &mut Parser) -> (String, Vec<String>) {
    // Case 1: raw already ends with "." and next token is "{"
    // e.g. tokens: ["id.", "{", "u", "}", ...]
    if raw.ends_with('.') && p.at("{") {
        let base = raw.trim_end_matches('.').to_string();
        p.consume("{");
        let mut ps = Vec::new();
        while !p.at("}") { ps.push(p.next_tok()); }
        p.consume("}");
        return (base, ps);
    }
    // Case 2: raw contains ".{" but tokenizer split it differently
    // Just use raw as name, check for "{" separately
    if p.at("{") {
        // peek ahead to see if this is a universe param block
        // (heuristic: if after { we see ident } :  then it's universe params)
        p.consume("{");
        let mut ps = Vec::new();
        while !p.at("}") { ps.push(p.next_tok()); }
        p.consume("}");
        return (raw, ps);
    }
    (raw, vec![])
}

pub fn run_script(script: &str, elab: &mut Elaborator) {
    let tokens = tokenize(script);
    let mut p = Parser { tokens, pos: 0 };

    while !p.eof() {
        let cmd = p.next_tok();
        match cmd.as_str() {
            "universe" => {
                // universe u v w
                // just skip — universe params are declared per-def
                while !p.eof() && !is_terminator(p.peek().unwrap()) {
                    p.next_tok();
                }
            }
            "inductive" => {
                let raw_name = p.next_tok();
                let (name, uparams) = parse_name_uparams(raw_name, &mut p);
                p.consume(":");
                let ty_pre = parse_expr(&mut p);
                let ty = elab.elab(&ty_pre, None, &uparams).unwrap();
                elab.env.inductives.insert(name.clone(), (uparams.clone(), ty));
                p.consume("where");
                let mut tag = 0;
                while !p.eof() && p.at("|") {
                    p.consume("|");
                    let ctor_name = p.next_tok();
                    p.consume(":");
                    let ctor_ty_pre = parse_expr(&mut p);
                    let ctor_ty = elab.elab(&ctor_ty_pre, None, &uparams).unwrap();
                    elab.env.ctors.insert(
                        ctor_name.clone(),
                        (name.clone(), tag, uparams.clone(), ctor_ty.clone()),
                    );
                    elab.env.inductives.insert(ctor_name.clone(), (uparams.clone(), ctor_ty));
                    tag += 1;
                }
                println!("=> Defined inductive: {}", name);
            }
            "def" => {
                // Parse name and optional universe params: id or id.{u v}
                let raw_name = p.next_tok();
                let (name, uparams) = parse_name_uparams(raw_name, &mut p);
                p.consume(":");
                let ty_pre = parse_expr(&mut p);
                p.consume(":=");
                let val_pre = parse_expr(&mut p);
                match elab.elab_def(&name, &uparams, &ty_pre, &val_pre) {
                    Ok(_) => println!("=> Defined: {}", name),
                    Err(e) => println!("Error in def {}: {}", name, e),
                }
            }
            "#eval" => {
                let pre = parse_expr(&mut p);
                match elab.elab(&pre, None, &[]) {
                    Ok(mut expr) => {
                        elab.apply_mvar_sols(&mut expr);
                        elab.fvars_to_bvars(&mut expr);
                        Kernel::new(&elab.env).nf(&mut expr);
                        println!("=> {}", pretty_expr(&expr, &elab.env));
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            "#check" => {
                let pre = parse_expr(&mut p);
                match elab.elab(&pre, None, &[]) {
                    Ok(mut expr) => {
                        elab.apply_mvar_sols(&mut expr);
                        elab.fvars_to_bvars(&mut expr);
                        match Kernel::new(&elab.env).infer(&expr, &mut LocalCtx::new()) {
                            Ok(ty) => println!("=> {} : {}",
                                pretty_expr(&expr, &elab.env),
                                pretty_expr(&ty, &elab.env)),
                            Err(e) => println!("Type error: {}", e),
                        }
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            _ => panic!("Unknown command: {}", cmd),
        }
    }
}

// ============================================================
// Main — test suite
// ============================================================

fn main() {
    let mut elab = Elaborator::new();

    // ---- Bool -----------------------------------------------
    run_script(r#"
        inductive Bool : Prop where
          | Bool.true  : Bool
          | Bool.false : Bool

        def not : Bool -> Bool :=
          fun (b : Bool) =>
            match b with
            | Bool.true  => Bool.false
            | Bool.false => Bool.true

        #eval not Bool.true
        #eval not Bool.false
        #check not
    "#, &mut elab);

    // ---- Nat ------------------------------------------------
    run_script(r#"
        inductive Nat : Type where
          | Nat.zero : Nat
          | Nat.succ : Nat -> Nat

        -- Nat literals
        #eval 0
        #eval 3

        def add : Nat -> Nat -> Nat :=
          fix add_fn : Nat -> Nat -> Nat =>
            fun (n : Nat) => fun (m : Nat) =>
              match n with
              | Nat.zero        => m
              | Nat.succ n_prev => Nat.succ (add_fn n_prev m)

        #eval add 2 3
        #check add

        def mul : Nat -> Nat -> Nat :=
          fix mul_fn : Nat -> Nat -> Nat =>
            fun (n : Nat) => fun (m : Nat) =>
              match n with
              | Nat.zero        => 0
              | Nat.succ n_prev => add m (mul_fn n_prev m)

        #eval mul 3 4
    "#, &mut elab);

    // ---- Polymorphic identity with universe params -----------
    run_script(r#"
        def id.{u} : {α : Sort u} -> α -> α :=
          fun {α : Sort u} => fun (x : α) => x

        #eval id 42
        #eval id Bool.true
        #check id
    "#, &mut elab);

    // ---- NatList (monomorphic) to test list basics ----------
    run_script(r#"
        inductive NatList : Type where
          | NatList.nil  : NatList
          | NatList.cons : Nat -> NatList -> NatList

        def NatList.length : NatList -> Nat :=
          fix len : NatList -> Nat =>
            fun (xs : NatList) =>
              match xs with
              | NatList.nil      => 0
              | NatList.cons _ t => Nat.succ (len t)

        #eval NatList.length (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))

        def NatList.sum : NatList -> Nat :=
          fix f : NatList -> Nat =>
            fun (xs : NatList) =>
              match xs with
              | NatList.nil      => 0
              | NatList.cons h t => add h (f t)

        #eval NatList.sum (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))
    "#, &mut elab);
}