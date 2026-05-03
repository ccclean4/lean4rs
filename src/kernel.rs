use std::collections::HashMap;
use crate::expr::{Expr, BinderInfo};
use crate::level::Level;

#[derive(Clone)]
pub struct GlobalEnv {
    pub inductives: HashMap<String, (Vec<String>, Expr)>,
    pub ctors: HashMap<String, (String, usize, Vec<String>, Expr)>,
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

#[derive(Clone)]
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

    pub fn whnf(&self, expr: &mut Expr) {
        let mut next: Option<Expr> = None;
        match expr {
            Expr::Const(name, lvls) => {
                if let Some((params, _, val)) = self.env.defs.get(name) {
                    let mut v = val.clone();
                    let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                    v.subst_levels(&substs);
                    next = Some(v);
                }
            }
            Expr::Let(_, val, body) => {
                let mut b = *body.clone();
                b.subst(0, val);
                next = Some(b);
            }
            Expr::App(f, arg) => {
                self.whnf(f);
                match f.as_mut() {
                    Expr::Lam(_, _, body) => {
                        let mut b = *body.clone();
                        b.subst(0, arg);
                        next = Some(b);
                    }
                    Expr::Fix(_, body) => {
                        let mut b = *body.clone();
                        self.whnf(&mut b);
                        b.subst(0, arg);
                        next = Some(b);
                    }
                    _ => {}
                }
            }
            Expr::Match(ind_name, target, _motive, branches) => {
                self.whnf(target);
                let (head, _args) = target.get_app_fn_args();
                if let Expr::Constructor(_, tag, _) = head {
                    if self.env.ctor_tag_of(ind_name, *tag).is_some() && *tag < branches.len() {
                        next = Some(branches[*tag].clone());
                    }
                }
            }
            _ => {}
        }
        if let Some(mut n) = next { self.whnf(&mut n); *expr = n; }
    }

    pub fn nf(&self, expr: &mut Expr) {
        self.whnf(expr);
        match expr {
            Expr::App(f, a) => { self.nf(f); self.nf(a); }
            Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Fix(ty, body) => {
                self.nf(ty); self.nf(body);
            }
            Expr::Let(ty, val, body) => { self.nf(ty); self.nf(val); self.nf(body); }
            Expr::Match(_, target, motive, branches) => {
                self.nf(target); self.nf(motive);
                for b in branches { self.nf(b); }
            }
            _ => {}
        }
    }

    pub fn struct_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (a, b) {
            (Expr::BVar(i), Expr::BVar(j)) => i == j,
            (Expr::FVar(i), Expr::FVar(j)) => i == j,
            (Expr::MVar(i), Expr::MVar(j)) => i == j,
            (Expr::Sort(l1), Expr::Sort(l2)) => l1.normalize() == l2.normalize(),
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (Expr::Inductive(n1, ls1), Expr::Inductive(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (Expr::Constructor(n1, t1, ls1), Expr::Constructor(n2, t2, ls2)) =>
                n1 == n2 && t1 == t2 && ls1 == ls2,
            (Expr::App(f1, a1), Expr::App(f2, a2)) =>
                self.struct_eq(f1, f2) && self.struct_eq(a1, a2),
            (Expr::Lam(bi1, ty1, b1), Expr::Lam(bi2, ty2, b2))
            | (Expr::Pi(bi1, ty1, b1), Expr::Pi(bi2, ty2, b2)) =>
                bi1 == bi2 && self.struct_eq(ty1, ty2) && self.struct_eq(b1, b2),
            (Expr::Fix(ty1, b1), Expr::Fix(ty2, b2)) =>
                self.struct_eq(ty1, ty2) && self.struct_eq(b1, b2),
            (Expr::Let(ty1, v1, b1), Expr::Let(ty2, v2, b2)) =>
                self.struct_eq(ty1, ty2) && self.struct_eq(v1, v2) && self.struct_eq(b1, b2),
            _ => false,
        }
    }

    pub fn def_eq(&self, e1: &Expr, e2: &Expr) -> bool {
        let mut w1 = e1.clone(); self.nf(&mut w1);
        let mut w2 = e2.clone(); self.nf(&mut w2);
        self.struct_eq(&w1, &w2)
    }

    pub fn infer(&self, expr: &Expr, lctx: &mut LocalCtx) -> Result<Expr, String> {
        match expr {
            Expr::BVar(n) => {
                let mut ty = lctx.get(*n)
                    .ok_or_else(|| format!("Unbound BVar({})", n))?.clone();
                ty.lift(*n + 1, 0);
                Ok(ty)
            }
            Expr::FVar(_) => Err("FVar should not reach kernel".into()),
            Expr::MVar(_) => Err("Unsolved metavariable in kernel check".into()),
            Expr::Sort(l) => Ok(Expr::Sort(Level::Succ(Box::new(l.clone())))),
            Expr::Const(name, lvls) => {
                let (params, ty, _) = self.env.defs.get(name)
                    .ok_or_else(|| format!("Unknown constant: {}", name))?;
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            Expr::Inductive(name, lvls) => {
                let (params, ty) = self.env.inductives.get(name)
                    .ok_or_else(|| format!("Unknown inductive: {}", name))?;
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            Expr::Constructor(ind, tag, lvls) => {
                let ctor_name = self.env.ctor_tag_of(ind, *tag)
                    .ok_or_else(|| format!("Unknown constructor {}.{}", ind, tag))?;
                let (_, _, params, ty) = self.env.ctors.get(ctor_name).unwrap();
                let mut t = ty.clone();
                let substs: Vec<_> = params.iter().cloned().zip(lvls.iter().cloned()).collect();
                t.subst_levels(&substs);
                Ok(t)
            }
            Expr::App(f, arg) => {
                let mut f_ty = self.infer(f, lctx)?;
                self.whnf(&mut f_ty);
                match f_ty {
                    Expr::Pi(_, param_ty, ret_ty) => {
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
            Expr::Lam(bi, ty, body) => {
                self.infer(ty, lctx)?;
                lctx.push(*ty.clone());
                let body_ty = self.infer(body, lctx)?;
                lctx.pop();
                Ok(Expr::Pi(bi.clone(), ty.clone(), Box::new(body_ty)))
            }
            Expr::Pi(_, ty, body) => {
                let s1 = self.infer(ty, lctx)?;
                lctx.push(*ty.clone());
                let s2 = self.infer(body, lctx)?;
                lctx.pop();
                let l1 = sort_level(s1).ok_or("Pi domain not a Sort")?;
                let l2 = sort_level(s2).ok_or("Pi codomain not a Sort")?;
                let l = Level::IMax(Box::new(l1), Box::new(l2)).normalize();
                Ok(Expr::Sort(l))
            }
            Expr::Let(ty, val, body) => {
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
            Expr::Fix(ty, body) => {
                lctx.push(*ty.clone());
                let body_ty = self.infer(body, lctx)?;
                lctx.pop();
                let fix_expr = Expr::Fix(ty.clone(), body.clone());
                let mut closed = body_ty;
                closed.subst(0, &fix_expr);
                if !self.def_eq(&closed, ty) {
                    return Err("Fixpoint type mismatch".into());
                }
                Ok(*ty.clone())
            }
            Expr::Match(_, target, motive, _) => {
                let mut motive_whnf = *motive.clone();
                self.whnf(&mut motive_whnf);
                match motive_whnf {
                    Expr::Lam(_, _, _) => {
                        let mut result_ty = Expr::App(motive.clone(), target.clone());
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
    if let Expr::Sort(l) = e { Some(l) } else { None }
}

#[allow(dead_code)]
pub fn pretty_expr(expr: &Expr, env: &GlobalEnv) -> String {
    use crate::expr::BinderInfo::*;
    use crate::expr::Expr::*;

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