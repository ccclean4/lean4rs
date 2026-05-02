use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    BVar(usize),
    Sort(usize),
    Const(String),
    App(Box<Expr>, Box<Expr>),
    Lam(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Box<Expr>),
    Let(Box<Expr>, Box<Expr>, Box<Expr>),
    Fix(Box<Expr>, Box<Expr>),
    Inductive(String),
    Constructor(String, usize),
    Match(String, Box<Expr>, Box<Expr>, Vec<Expr>),
}

use Expr::*;

impl Expr {
    fn get_app_fn_args(&self) -> (&Expr, Vec<Expr>) {
        let mut curr = self;
        let mut args = Vec::new();
        while let App(f, arg) = curr {
            args.push(*arg.clone());
            curr = f.as_ref();
        }
        args.reverse();
        (curr, args)
    }

    fn lift(&mut self, amount: usize, threshold: usize) {
        match self {
            BVar(n) => { if *n >= threshold { *n += amount; } }
            Sort(_) | Inductive(_) | Constructor(_, _) | Const(_) => {}
            App(f, arg) => { f.lift(amount, threshold); arg.lift(amount, threshold); }
            Lam(ty, body) | Pi(ty, body) | Fix(ty, body) => {
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
                motive.lift(amount, threshold);
                for b in branches { b.lift(amount, threshold); }
            }
        }
    }

    fn subst(&mut self, var_idx: usize, value: &Expr) {
        match self {
            BVar(n) => {
                if *n == var_idx { *self = value.clone(); } 
                else if *n > var_idx { *n -= 1; }
            }
            Sort(_) | Inductive(_) | Constructor(_, _) | Const(_) => {}
            App(f, arg) => { f.subst(var_idx, value); arg.subst(var_idx, value); }
            Lam(ty, body) | Pi(ty, body) | Fix(ty, body) => {
                ty.subst(var_idx, value);
                let mut shifted = value.clone(); shifted.lift(1, 0);
                body.subst(var_idx + 1, &shifted);
            }
            Let(ty, val, body) => {
                ty.subst(var_idx, value);
                val.subst(var_idx, value);
                let mut shifted = value.clone(); shifted.lift(1, 0);
                body.subst(var_idx + 1, &shifted);
            }
            Match(_, target, motive, branches) => {
                target.subst(var_idx, value);
                motive.subst(var_idx, value);
                for b in branches { b.subst(var_idx, value); }
            }
        }
    }

    fn whnf(&mut self, ctx: &Context) {
        let mut new_self = None;
        match self {
            Const(name) => {
                if let Some((_, val)) = ctx.defs.get(name) { new_self = Some(val.clone()); }
            }
            Let(_, val, body) => {
                let mut new_body = *body.clone();
                new_body.subst(0, val);
                new_self = Some(new_body);
            }
            App(f, arg) => {
                f.whnf(ctx); 
                if let Lam(_ty, body) = &**f {
                    let mut new_body = *body.clone();
                    new_body.subst(0, arg);
                    new_self = Some(new_body);
                } else if let Fix(_ty, body) = &**f {
                    let mut new_body = *body.clone();
                    new_body.subst(0, &*f.clone());
                    new_self = Some(App(Box::new(new_body), arg.clone()));
                }
            }
            Match(ind_name, target, _motive, branches) => {
                target.whnf(ctx);
                let (head, args) = target.get_app_fn_args();
                if let Constructor(c_name, tag) = head {
                    if c_name == ind_name && *tag < branches.len() {
                        let mut res = branches[*tag].clone();
                        for arg in args { res = App(Box::new(res), Box::new(arg)); }
                        new_self = Some(res);
                    }
                }
            }
            _ => {}
        }
        if let Some(mut ns) = new_self { ns.whnf(ctx); *self = ns; }
    }

    fn nf(&mut self, ctx: &Context) {
        self.whnf(ctx);
        match self {
            App(f, arg) => { f.nf(ctx); arg.nf(ctx); }
            Lam(ty, body) | Pi(ty, body) | Fix(ty, body) => { ty.nf(ctx); body.nf(ctx); }
            Let(ty, val, body) => { ty.nf(ctx); val.nf(ctx); body.nf(ctx); }
            Match(_, target, motive, branches) => {
                target.nf(ctx); motive.nf(ctx);
                for b in branches { b.nf(ctx); }
            }
            _ => {}
        }
    }
}

pub struct Context {
    types: Vec<Expr>,
    pub env: HashMap<String, Expr>,           
    pub ctors: HashMap<String, (String, usize)>, // 記錄 Constructor 名稱 -> (所屬 Inductive, Tag索引)
    pub defs: HashMap<String, (Expr, Expr)>,  
}

impl Context {
    pub fn new() -> Self {
        Context { types: Vec::new(), env: HashMap::new(), ctors: HashMap::new(), defs: HashMap::new() }
    }

    pub fn infer_type(&mut self, expr: &Expr) -> Result<Expr, String> {
        match expr {
            BVar(n) => {
                if *n < self.types.len() {
                    let mut ty = self.types[self.types.len() - 1 - n].clone();
                    ty.lift(*n + 1, 0); Ok(ty)
                } else { Err(format!("Unbound variable: {}", n)) }
            }
            Sort(u) => Ok(Sort(u + 1)),
            Const(name) => self.defs.get(name).map(|(ty, _)| ty.clone()).ok_or_else(|| format!("Unknown Const: {}", name)),
            Inductive(name) => self.env.get(name).cloned().ok_or_else(|| format!("Unknown Inductive: {}", name)),
            Constructor(name, tag) => {
                let search_name = self.ctors.iter().find(|(_, (i, t))| i == name && t == tag).map(|(k, _)| k).unwrap();
                Ok(self.env.get(search_name).unwrap().clone())
            }
            App(f, arg) => {
                let mut f_ty = self.infer_type(f)?;
                f_ty.whnf(self);
                if let Pi(param_ty, ret_ty) = f_ty {
                    let arg_ty = self.infer_type(arg)?;
                    if !is_def_eq(&arg_ty, &param_ty, self) { return Err("Type mismatch".into()); }
                    let mut result_ty = *ret_ty.clone();
                    result_ty.subst(0, arg);
                    Ok(result_ty)
                } else { Err("Expected Pi type".into()) }
            }
            Lam(ty, body) => {
                self.infer_type(ty)?;
                self.types.push(*ty.clone());
                let body_ty = self.infer_type(body)?;
                self.types.pop();
                Ok(Pi(ty.clone(), Box::new(body_ty)))
            }
            Pi(ty, body) => {
                self.infer_type(ty)?;
                self.types.push(*ty.clone());
                self.infer_type(body)?;
                self.types.pop();
                Ok(Sort(0))
            }
            Let(ty, val, body) => {
                let val_ty = self.infer_type(val)?;
                if !is_def_eq(&val_ty, ty, self) { return Err("Let type mismatch".into()); }
                self.types.push(*ty.clone());
                let mut body_ty = self.infer_type(body)?;
                self.types.pop();
                body_ty.subst(0, val);
                Ok(body_ty)
            }
            Fix(ty, body) => {
                self.types.push(*ty.clone());
                let body_ty = self.infer_type(body)?;
                self.types.pop();
                let fix_expr = Fix(ty.clone(), body.clone());
                let mut closed_body_ty = body_ty.clone();
                closed_body_ty.subst(0, &fix_expr);
                let mut w1 = closed_body_ty.clone(); w1.nf(self);
                let mut w2 = *ty.clone(); w2.nf(self);
                // println!("closed_body_ty (nf): {:?}", w1);
                // println!("decl_ty        (nf): {:?}", w2);
                if !is_def_eq(&closed_body_ty, ty, self) {
                    return Err("Fixpoint type mismatch".into());
                }
                Ok(*ty.clone())
            }
            Match(_, target, motive, _) => {
                // If motive is already a type (not a function), return it directly.
                // If motive is a function (Pi-abstracted over scrutinee), apply it.
                let mut motive_whnf = *motive.clone();
                motive_whnf.whnf(self);
                match motive_whnf {
                    Lam(_, _) => {
                        let mut result_ty = App(motive.clone(), target.clone());
                        result_ty.whnf(self);
                        Ok(result_ty)
                    }
                    _ => Ok(*motive.clone())
                }
            }
        }
    }
}

fn structural_eq(e1: &Expr, e2: &Expr, ctx: &Context) -> bool {
    match (e1, e2) {
        (BVar(n1), BVar(n2)) => n1 == n2,
        (Sort(u1), Sort(u2)) => u1 == u2,
        (Const(n1), Const(n2)) => n1 == n2,
        (Inductive(n1), Inductive(n2)) => n1 == n2,
        (Constructor(n1, t1), Constructor(n2, t2)) => n1 == n2 && t1 == t2,
        (App(f1, a1), App(f2, a2)) =>
            structural_eq(f1, f2, ctx) && structural_eq(a1, a2, ctx),
        (Lam(t1, b1), Lam(t2, b2)) | (Pi(t1, b1), Pi(t2, b2)) | (Fix(t1, b1), Fix(t2, b2)) =>
            structural_eq(t1, t2, ctx) && structural_eq(b1, b2, ctx),
        (Let(t1, v1, b1), Let(t2, v2, b2)) =>
            structural_eq(t1, t2, ctx) && structural_eq(v1, v2, ctx) && structural_eq(b1, b2, ctx),
        _ => false,
    }
}

fn is_def_eq(e1: &Expr, e2: &Expr, ctx: &Context) -> bool {
    let mut w1 = e1.clone(); w1.nf(ctx);
    let mut w2 = e2.clone(); w2.nf(ctx);
    structural_eq(&w1, &w2, ctx)
}
// ==========================================
// 微型 Lean 4 解析器 (Recursive Descent)
// ==========================================
struct Parser { tokens: Vec<String>, pos: usize }

impl Parser {
    fn peek(&self) -> Option<&String> { self.tokens.get(self.pos) }
    fn next_tok(&mut self) -> String { let t = self.tokens[self.pos].clone(); self.pos += 1; t }
    fn consume(&mut self, expected: &str) {
        let t = self.next_tok();
        if t != expected { panic!("Expected '{}', got '{}'", expected, t); }
    }
    fn eof(&self) -> bool { self.pos >= self.tokens.len() }
}

fn is_terminator(t: &str) -> bool {
    matches!(t, ")" | "->" | "=>" | ":=" | ";" | "|" | "," | "with" | "return" | "where" | "def" | "inductive" | "#eval" | "#check")
}

fn parse_atom(p: &mut Parser, locals: &mut Vec<String>, ctx: &Context) -> Expr {
    let tok = p.next_tok();
    if tok == "(" {
        let e = parse_expr(p, locals, ctx);
        p.consume(")");
        return e;
    }
    if tok == "Sort" { return Sort(p.next_tok().parse().unwrap()); }
    if let Some(idx) = locals.iter().rev().position(|x| x == &tok) { return BVar(idx); }
    if let Some((ind, tag)) = ctx.ctors.get(&tok) { return Constructor(ind.clone(), *tag); }
    if ctx.env.contains_key(&tok) { return Inductive(tok); }
    if ctx.defs.contains_key(&tok) { return Const(tok); }
    panic!("Unknown identifier: {}", tok);
}

fn parse_app(p: &mut Parser, locals: &mut Vec<String>, ctx: &Context) -> Expr {
    let mut res = parse_atom(p, locals, ctx);
    while !p.eof() && !is_terminator(p.peek().unwrap()) {
        res = App(Box::new(res), Box::new(parse_atom(p, locals, ctx)));
    }
    res
}

fn parse_arrow(p: &mut Parser, locals: &mut Vec<String>, ctx: &Context) -> Expr {
    let mut res = parse_app(p, locals, ctx);
    while p.peek().map(|s| s.as_str()) == Some("->") {
        p.consume("->");
        let right = parse_arrow(p, locals, ctx);
        let mut body = right; 
        body.lift(1, 0);
        res = Pi(Box::new(res), Box::new(body));
    }
    res
}

fn parse_expr(p: &mut Parser, locals: &mut Vec<String>, ctx: &Context) -> Expr {
    if let Some(tok) = p.peek() {
        match tok.as_str() {
            "fun" => {
                p.consume("fun"); p.consume("("); let x = p.next_tok(); p.consume(":");
                let ty = parse_expr(p, locals, ctx); p.consume(")"); p.consume("=>");
                locals.push(x); let body = parse_expr(p, locals, ctx); locals.pop();
                return Lam(Box::new(ty), Box::new(body));
            }
            "fix" => {
                p.consume("fix"); let f = p.next_tok(); p.consume(":");
                let ty = parse_expr(p, locals, ctx); p.consume("=>");
                locals.push(f); let body = parse_expr(p, locals, ctx); locals.pop();
                return Fix(Box::new(ty), Box::new(body));
            }
            "let" => {
                p.consume("let"); let x = p.next_tok(); p.consume(":");
                let ty = parse_expr(p, locals, ctx); p.consume(":=");
                let val = parse_expr(p, locals, ctx); p.consume(";");
                locals.push(x); let body = parse_expr(p, locals, ctx); locals.pop();
                return Let(Box::new(ty), Box::new(val), Box::new(body));
            }
            "match" => {
                p.consume("match"); let ind = p.next_tok(); p.consume(",");
                let target = parse_expr(p, locals, ctx); p.consume("return");
                let motive = parse_expr(p, locals, ctx); p.consume("with");
                let mut branches = Vec::new();
                while !p.eof() && p.peek().map(|s| s.as_str()) == Some("|") {
                    p.consume("|"); p.next_tok(); p.consume("=>"); // 略過 constructor name
                    branches.push(parse_expr(p, locals, ctx));
                }
                return Match(ind, Box::new(target), Box::new(motive), branches);
            }
            _ => return parse_arrow(p, locals, ctx),
        }
    }
    panic!("Unexpected EOF")
}

fn run_lean_script(script: &str, ctx: &mut Context) {
    let cleaned_script = script.lines()
        .map(|line| if let Some(idx) = line.find("--") { &line[..idx] } else { line })
        .collect::<Vec<_>>().join(" ");

    // 我們只替換保證安全的符號，避免破壞 :=
    let s = cleaned_script
        .replace("(", " ( ")
        .replace(")", " ) ")
        .replace(";", " ; ")
        .replace("|", " | ");

    let tokens: Vec<String> = s.split_whitespace().map(|x| x.to_string()).collect();
    let mut p = Parser { tokens, pos: 0 };

    while !p.eof() {
        let cmd = p.next_tok();
        match cmd.as_str() {
            "inductive" => {
                let name = p.next_tok(); p.consume(":");
                let ty = parse_expr(&mut p, &mut vec![], ctx); p.consume("where");
                ctx.env.insert(name.clone(), ty);
                let mut tag = 0;
                while !p.eof() && p.peek().map(|s| s.as_str()) == Some("|") {
                    p.consume("|"); let ctor_name = p.next_tok(); p.consume(":");
                    let ctor_ty = parse_expr(&mut p, &mut vec![], ctx);
                    ctx.env.insert(ctor_name.clone(), ctor_ty);
                    ctx.ctors.insert(ctor_name, (name.clone(), tag));
                    tag += 1;
                }
                println!("=> Defined Inductive: {}", name);
            }
            "def" => {
                let name = p.next_tok(); p.consume(":");
                let ty = parse_expr(&mut p, &mut vec![], ctx); p.consume(":=");
                let val = parse_expr(&mut p, &mut vec![], ctx);
                ctx.infer_type(&val).unwrap();
                ctx.defs.insert(name.clone(), (ty, val));
                println!("=> Defined: {}", name);
            }
            "#eval" | "#check" => {
                let mut expr = parse_expr(&mut p, &mut vec![], ctx);
                if cmd == "#check" {
                    println!("=> Check: {:?}", ctx.infer_type(&expr).unwrap());
                } else {
                    expr.nf(ctx);
                    println!("=> Eval: {:?}", expr);
                }
            }
            _ => panic!("Unknown command: {}", cmd),
        }
    }
}

fn main() {
    let mut ctx = Context::new();

    let bool_lean = r#"
        -- 布林值定義
        inductive Bool : Sort 0 where
          | Bool.true : Bool
          | Bool.false : Bool

        -- NOT 函數
        def not : Bool -> Bool :=
          fun (b : Bool) =>
            match Bool , b return Bool with
            | Bool.true => Bool.false
            | Bool.false => Bool.true

        -- 測試: not true
        #eval not Bool.true
    "#;

    let nat_lean = r#"
        -- 自然數定義
        inductive Nat : Sort 0 where
          | Nat.zero : Nat
          | Nat.succ : Nat -> Nat

        -- Let 測試
        #eval let x : Nat := Nat.zero ; Nat.succ x

        -- Add 遞迴加法函數
        def add : Nat -> Nat -> Nat :=
          fix add_fn : Nat -> Nat -> Nat =>
            fun (n : Nat) => fun (m : Nat) =>
              match Nat , n return Nat with
              | Nat.zero => m
              | Nat.succ => fun (n_prev : Nat) => Nat.succ (add_fn n_prev m)

        -- 測試 1 + 1 (succ zero + succ zero)
        #eval add (Nat.succ Nat.zero) (Nat.succ Nat.zero)
    "#;

    println!("--- 載入 bool.lean ---");
    run_lean_script(bool_lean, &mut ctx);

    println!("\n--- 載入 nat.lean ---");
    run_lean_script(nat_lean, &mut ctx);
}