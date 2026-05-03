use std::collections::HashMap;
use crate::expr::{Expr, BinderInfo};
use crate::level::Level;
use crate::kernel::{GlobalEnv, Kernel, LocalCtx};

#[derive(Debug, Clone)]
pub enum PreExpr {
    Var(String),
    Hole,
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
    mvar_types: Vec<Expr>,
    mvar_sols: Vec<Option<Expr>>,
    uvar_count: usize,
    uvar_sols: HashMap<String, Level>,
    fvar_types: Vec<Expr>,
    fvar_names: Vec<String>,
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
            name_env: Vec::new(),
        }
    }

    fn fresh_mvar(&mut self, ty: Expr) -> Expr {
        let id = self.mvar_types.len();
        self.mvar_types.push(ty);
        self.mvar_sols.push(None);
        Expr::MVar(id)
    }

    fn fresh_uvar(&mut self) -> Level {
        let name = format!("u{}", self.uvar_count);
        self.uvar_count += 1;
        Level::UVar(name)
    }

    pub fn apply_mvar_sols(&self, expr: &mut Expr) {
        for (i, sol) in self.mvar_sols.iter().enumerate() {
            if let Some(v) = sol {
                expr.subst_mvar(i, v);
            }
        }
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

    fn push_fvar(&mut self, name: String, ty: Expr) -> usize {
        let id = self.fvar_types.len();
        self.fvar_types.push(ty);
        self.fvar_names.push(name.clone());
        self.name_env.push((name, id));
        id
    }

    fn pop_fvar(&mut self) {
        self.name_env.pop();
    }

    fn lookup_name(&self, name: &str) -> Option<usize> {
        self.name_env.iter().rev()
            .find(|(n, _)| n == name)
            .map(|(_, id)| *id)
    }

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
                Ok(())
            }
            _ => Err(format!("Universe mismatch: {} vs {}", l1n.pretty(), l2n.pretty())),
        }
    }

    fn unify(&mut self, e1: &Expr, e2: &Expr) -> Result<(), String> {
        use crate::kernel::pretty_expr;
        let mut a = e1.clone(); self.apply_mvar_sols(&mut a);
        let mut b = e2.clone(); self.apply_mvar_sols(&mut b);
        let k = Kernel::new(&self.env);
        k.whnf(&mut a); k.whnf(&mut b);
        match (&a.clone(), &b.clone()) {
            (Expr::MVar(i), _) => self.solve_mvar(*i, b),
            (_, Expr::MVar(i)) => self.solve_mvar(*i, a),
            (Expr::Sort(l1), Expr::Sort(l2)) => self.unify_level(l1, l2),
            (Expr::BVar(i), Expr::BVar(j)) if i == j => Ok(()),
            (Expr::FVar(i), Expr::FVar(j)) if i == j => Ok(()),
            (Expr::Inductive(n1, ls1), Expr::Inductive(n2, ls2)) if n1 == n2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (Expr::Constructor(n1, t1, ls1), Expr::Constructor(n2, t2, ls2)) if n1 == n2 && t1 == t2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) if n1 == n2 => {
                for (l1, l2) in ls1.iter().zip(ls2.iter()) { self.unify_level(l1, l2)?; }
                Ok(())
            }
            (Expr::App(f1, a1), Expr::App(f2, a2)) => {
                self.unify(f1, f2)?; self.unify(a1, a2)
            }
            (Expr::Lam(_, ty1, b1), Expr::Lam(_, ty2, b2))
            | (Expr::Pi(_, ty1, b1), Expr::Pi(_, ty2, b2)) => {
                self.unify(ty1, ty2)?; self.unify(b1, b2)
            }
            _ => {
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

    fn fvar_to_bvar(&self, expr: &mut Expr, fvar_id: usize, depth: usize) {
        match expr {
            Expr::FVar(id) => { if *id == fvar_id { *expr = Expr::BVar(depth); } }
            Expr::BVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Inductive(_, _)
            | Expr::Constructor(_, _, _) | Expr::Const(_, _) => {}
            Expr::App(f, a) => {
                self.fvar_to_bvar(f, fvar_id, depth);
                self.fvar_to_bvar(a, fvar_id, depth);
            }
            Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Fix(ty, body) => {
                self.fvar_to_bvar(ty, fvar_id, depth);
                self.fvar_to_bvar(body, fvar_id, depth + 1);
            }
            Expr::Let(ty, val, body) => {
                self.fvar_to_bvar(ty, fvar_id, depth);
                self.fvar_to_bvar(val, fvar_id, depth);
                self.fvar_to_bvar(body, fvar_id, depth + 1);
            }
            Expr::Match(_, target, motive, branches) => {
                self.fvar_to_bvar(target, fvar_id, depth);
                self.fvar_to_bvar(motive, fvar_id, depth + 1);
                for b in branches { self.fvar_to_bvar(b, fvar_id, depth); }
            }
        }
    }

    fn build_lctx(&self) -> LocalCtx {
        let mut lctx = LocalCtx::new();
        for (_, id) in &self.name_env {
            lctx.push(self.fvar_types[*id].clone());
        }
        lctx
    }

    pub fn elab(&mut self, pre: &PreExpr, expected_ty: Option<&Expr>,
                uparams: &[String]) -> Result<Expr, String> {
        match pre {
            PreExpr::Hole => {
                let ty = expected_ty.cloned().unwrap_or_else(|| {
                    let u = self.fresh_uvar();
                    Expr::Sort(u)
                });
                Ok(self.fresh_mvar(ty))
            }

            PreExpr::NatLit(n) => {
                let zero = Expr::Constructor("Nat".into(), 0, vec![]);
                Ok((0..*n).fold(zero, |acc, _| {
                    Expr::App(Box::new(Expr::Constructor("Nat".into(), 1, vec![])), Box::new(acc))
                }))
            }

            PreExpr::Sort(pl) => {
                let l = pl.to_level(uparams);
                Ok(Expr::Sort(l))
            }

            PreExpr::Var(name) => {
                if let Some(fvar_id) = self.lookup_name(name) {
                    return Ok(Expr::FVar(fvar_id));
                }
                eprintln!("DEBUG Var: name='{}' inductives_keys={:?}", name, self.env.inductives.keys().collect::<Vec<_>>());
                if !name.contains('.') {
                    if let Some((params, _)) = self.env.inductives.get(name) {
                        let name_clone = name.clone();
                        let lvls: Vec<Level> = params.iter()
                            .map(|p| Level::Param(p.clone()))
                            .collect();
                        return Ok(Expr::Inductive(name_clone, lvls));
                    }
                }
                if let Some((ind, tag, params, _)) = self.env.ctors.get(name) {
                    let ind_clone = ind.clone();
                    let tag_clone = *tag;
                    let lvls: Vec<Level> = params.iter()
                        .map(|p| Level::Param(p.clone()))
                        .collect();
                    return Ok(Expr::Constructor(ind_clone, tag_clone, lvls));
                }
                if let Some((params, _, _)) = self.env.defs.get(name) {
                    let name_clone = name.clone();
                    let lvls: Vec<Level> = params.iter()
                        .map(|p| Level::Param(p.clone()))
                        .collect();
                    return Ok(Expr::Const(name_clone, lvls));
                }
                Err(format!("Unknown identifier: {}", name))
            }

            PreExpr::Lam(bi, param_name, param_ty_pre, body_pre) => {
                let param_ty = self.elab(param_ty_pre, None, uparams)?;
                let fvar_id = self.push_fvar(param_name.clone(), param_ty.clone());
                let body_exp = expected_ty.and_then(|ty| {
                    let mut w = ty.clone();
                    let k = Kernel::new(&self.env);
                    k.whnf(&mut w);
                    if let Expr::Pi(_, _, ret) = w { Some(*ret) } else { None }
                });
                let mut body = self.elab(body_pre, body_exp.as_ref(), uparams)?;
                self.pop_fvar();
                self.fvar_to_bvar(&mut body, fvar_id, 0);
                let mut pty = param_ty.clone();
                self.fvar_to_bvar(&mut pty, fvar_id, 0);
                Ok(Expr::Lam(bi.clone(), Box::new(pty), Box::new(body)))
            }

            PreExpr::Pi(bi, param_name, param_ty_pre, body_pre) => {
                let param_ty = self.elab(param_ty_pre, None, uparams)?;
                let fvar_id = self.push_fvar(param_name.clone(), param_ty.clone());
                let mut body = self.elab(body_pre, None, uparams)?;
                self.pop_fvar();
                self.fvar_to_bvar(&mut body, fvar_id, 0);
                let mut pty = param_ty.clone();
                self.fvar_to_bvar(&mut pty, fvar_id, 0);
                Ok(Expr::Pi(bi.clone(), Box::new(pty), Box::new(body)))
            }

            PreExpr::Let(name, ty_pre, val_pre, body_pre) => {
                let ty = self.elab(ty_pre, None, uparams)?;
                let val = self.elab(val_pre, Some(&ty), uparams)?;
                let fvar_id = self.push_fvar(name.clone(), ty.clone());
                let mut body = self.elab(body_pre, expected_ty, uparams)?;
                self.pop_fvar();
                self.fvar_to_bvar(&mut body, fvar_id, 0);
                let mut ety = ty.clone();
                self.fvar_to_bvar(&mut ety, fvar_id, 0);
                let mut eval = val.clone();
                self.fvar_to_bvar(&mut eval, fvar_id, 0);
                Ok(Expr::Let(Box::new(ety), Box::new(eval), Box::new(body)))
            }

            PreExpr::Fix(fname, ty_pre, body_pre) => {
                let ty = self.elab(ty_pre, None, uparams)?;
                let fvar_id = self.push_fvar(fname.clone(), ty.clone());
                let mut body = self.elab(body_pre, Some(&ty), uparams)?;
                self.pop_fvar();
                self.fvar_to_bvar(&mut body, fvar_id, 0);
                let mut ety = ty.clone();
                self.fvar_to_bvar(&mut ety, fvar_id, 0);
                Ok(Expr::Fix(Box::new(ety), Box::new(body)))
            }

            PreExpr::App(f_pre, arg_pre) => {
                let f = self.elab(f_pre, None, uparams)?;
                let f_with_implicits = self.insert_implicits(f, uparams)?;
                let (f_expr, f_ty) = f_with_implicits;
                let mut f_ty_whnf = f_ty.clone();
                let k = Kernel::new(&self.env);
                k.whnf(&mut f_ty_whnf);
                let arg_exp_ty = if let Expr::Pi(_, param_ty, _) = &f_ty_whnf {
                    Some(*param_ty.clone())
                } else { None };
                let arg = self.elab(arg_pre, arg_exp_ty.as_ref(), uparams)?;
                if let Expr::Pi(_, param_ty, _) = &f_ty_whnf {
                    let arg_ty = {
                        let mut lctx = self.build_lctx();
                        let mut arg_k = arg.clone();
                        self.fvars_to_bvars(&mut arg_k);
                        Kernel::new(&self.env).infer(&arg_k, &mut lctx)?
                    };
                    self.unify(&arg_ty, param_ty)?;
                }
                Ok(Expr::App(Box::new(f_expr), Box::new(arg)))
            }

            PreExpr::Match(ind_name, target_pre, motive_pre, branches_pre) => {
                let target = self.elab(target_pre, None, uparams)?;
                let motive: Expr = if let Some(m_pre) = motive_pre {
                    self.elab(m_pre, None, uparams)?
                } else {
                    let uvar = self.fresh_uvar();
                    let ret_ty = self.fresh_mvar(Expr::Sort(uvar));
                    let mut lam_body = ret_ty;
                    lam_body.lift(1, 0);
                    let ind_ty = self.env.inductives.get(ind_name)
                        .map(|(_, t)| t.clone())
                        .unwrap_or(Expr::Sort(Level::Zero));
                    Expr::Lam(BinderInfo::Default, Box::new(ind_ty), Box::new(lam_body))
                };

                let mut branches: Vec<Expr> = Vec::new();
                for (ctor_name, binder_names, branch_body_pre) in branches_pre {
                    let (_, _, _, ctor_ty) = self.env.ctors.get(ctor_name)
                        .ok_or_else(|| format!("Unknown constructor: {}", ctor_name))?.clone();

                    let mut fvar_ids = Vec::new();
                    let mut cur_ty = ctor_ty.clone();
                    for bname in binder_names {
                        let k = Kernel::new(&self.env);
                        k.whnf(&mut cur_ty);
                        if let Expr::Pi(_, param_ty, ret) = cur_ty.clone() {
                            let fid = self.push_fvar(bname.clone(), *param_ty);
                            fvar_ids.push(fid);
                            cur_ty = *ret;
                        } else {
                            return Err(format!(
                                "Too many binders for constructor {}", ctor_name));
                        }
                    }
                    let mut branch_body = self.elab(branch_body_pre, None, uparams)?;
                    for (depth, fid) in fvar_ids.iter().rev().enumerate() {
                        self.pop_fvar();
                        self.fvar_to_bvar(&mut branch_body, *fid, depth);
                    }
                    for fid in fvar_ids.iter().rev() {
                        let bty = self.fvar_types[*fid].clone();
                        branch_body = Expr::Lam(BinderInfo::Default, Box::new(bty), Box::new(branch_body));
                    }
                    branches.push(branch_body);
                }

                let n_ctors = self.env.ctors.values()
                    .filter(|(i, _, _, _)| i == ind_name).count();
                while branches.len() < n_ctors {
                    let mv = self.fresh_mvar(Expr::Sort(Level::Zero));
                    branches.push(mv);
                }

                Ok(Expr::Match(ind_name.clone(), Box::new(target), Box::new(motive), branches))
            }
        }
    }

    fn insert_implicits(&mut self, f: Expr, _uparams: &[String])
        -> Result<(Expr, Expr), String>
    {
        let mut f_k = f.clone();
        self.fvars_to_bvars(&mut f_k);
        let mut lctx = self.build_lctx();
        let f_ty = Kernel::new(&self.env).infer(&f_k, &mut lctx)?;
        let mut result = f;
        let mut result_ty = f_ty;
        loop {
            let mut w = result_ty.clone();
            Kernel::new(&self.env).whnf(&mut w);
            if let Expr::Pi(BinderInfo::Implicit, param_ty, ret_ty) = w {
                let mv = self.fresh_mvar(*param_ty);
                result_ty = { let mut r = *ret_ty; r.subst(0, &mv); r };
                result = Expr::App(Box::new(result), Box::new(mv));
            } else if let Expr::Pi(BinderInfo::Instance, param_ty, ret_ty) = w {
                let mv = self.fresh_mvar(*param_ty);
                result_ty = { let mut r = *ret_ty; r.subst(0, &mv); r };
                result = Expr::App(Box::new(result), Box::new(mv));
            } else {
                break;
            }
        }
        Ok((result, result_ty))
    }

    pub fn fvars_to_bvars(&self, expr: &mut Expr) {
        let depth_map: HashMap<usize, usize> = self.name_env.iter().rev().enumerate()
            .map(|(depth, (_, id))| (*id, depth))
            .collect();
        fvars_to_bvars_inner(expr, &depth_map);
    }

    pub fn elab_def(&mut self, name: &str, uparams: &[String],
                    ty_pre: &PreExpr, val_pre: &PreExpr) -> Result<(), String> {
        self.env.defs.insert(name.to_string(), (uparams.to_vec(), Expr::Sort(Level::Zero), Expr::Sort(Level::Zero)));

        let ty = self.elab(ty_pre, None, uparams)?;
        let mut ty_k = ty.clone();
        self.apply_mvar_sols(&mut ty_k);

        let val = self.elab(val_pre, Some(&ty_k), uparams)?;
        let mut val_k = val.clone();
        self.apply_mvar_sols(&mut val_k);
        self.fvars_to_bvars(&mut val_k);

        let mut lctx = LocalCtx::new();
        Kernel::new(&self.env).infer(&val_k, &mut lctx)?;

        self.env.defs.insert(name.to_string(), (uparams.to_vec(), ty_k, val_k));
        Ok(())
    }
}

pub fn fvars_to_bvars_inner(expr: &mut Expr, dm: &HashMap<usize, usize>) {
    match expr {
        Expr::FVar(id) => {
            if let Some(depth) = dm.get(id) { *expr = Expr::BVar(*depth); }
        }
        Expr::BVar(_) | Expr::MVar(_) | Expr::Sort(_) | Expr::Inductive(_, _)
        | Expr::Constructor(_, _, _) | Expr::Const(_, _) => {}
        Expr::App(f, a) => { fvars_to_bvars_inner(f, dm); fvars_to_bvars_inner(a, dm); }
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Fix(ty, body) => {
            fvars_to_bvars_inner(ty, dm);
            let dm2: HashMap<usize, usize> = dm.iter().map(|(k, v)| (*k, v + 1)).collect();
            fvars_to_bvars_inner(body, &dm2);
        }
        Expr::Let(ty, val, body) => {
            fvars_to_bvars_inner(ty, dm);
            fvars_to_bvars_inner(val, dm);
            let dm2: HashMap<usize, usize> = dm.iter().map(|(k, v)| (*k, v + 1)).collect();
            fvars_to_bvars_inner(body, &dm2);
        }
        Expr::Match(_, target, motive, branches) => {
            fvars_to_bvars_inner(target, dm);
            let dm2: HashMap<usize, usize> = dm.iter().map(|(k, v)| (*k, v + 1)).collect();
            fvars_to_bvars_inner(motive, &dm2);
            for b in branches { fvars_to_bvars_inner(b, dm); }
        }
    }
}