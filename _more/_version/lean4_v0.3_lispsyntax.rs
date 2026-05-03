use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    BVar(usize),
    Sort(usize),
    Const(String), // 全域定義常數引用
    App(Box<Expr>, Box<Expr>),
    Lam(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Box<Expr>),
    Let(Box<Expr>, Box<Expr>, Box<Expr>), // ty, val, body
    Fix(Box<Expr>, Box<Expr>),            // ty, body
    Inductive(String),
    Constructor(String, usize),
    Match(String, Box<Expr>, Box<Expr>, Vec<Expr>), // ind_name, target, motive, branches
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

    /// WHNF 弱頭範式 (需傳入 Context 以展開全域定義 Const)
    fn whnf(&mut self, ctx: &Context) {
        let mut new_self = None;
        match self {
            Const(name) => {
                if let Some((_, val)) = ctx.defs.get(name) {
                    new_self = Some(val.clone()); // 展開定義 (Delta-reduction)
                }
            }
            Let(_, val, body) => {
                let mut new_body = *body.clone();
                new_body.subst(0, val);
                new_self = Some(new_body); // Zeta-reduction
            }
            App(f, arg) => {
                f.whnf(ctx); 
                if let Lam(_ty, body) = &**f {
                    let mut new_body = *body.clone();
                    new_body.subst(0, arg);
                    new_self = Some(new_body); // Beta-reduction
                } else if let Fix(_ty, body) = &**f {
                    // 惰性展開 Fixpoint：當 Fix 被呼叫時，將自身代入 body 中
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
                        new_self = Some(res); // Iota-reduction
                    }
                }
            }
            _ => {}
        }
        if let Some(mut ns) = new_self {
            ns.whnf(ctx);
            *self = ns;
        }
    }
}

pub struct Context {
    types: Vec<Expr>,
    pub env: HashMap<String, Expr>,           // 歸納類型與建構子簽名
    pub defs: HashMap<String, (Expr, Expr)>,  // 全域變數 (名稱 -> (型別, 數值))
}

impl Context {
    pub fn new() -> Self {
        Context { types: Vec::new(), env: HashMap::new(), defs: HashMap::new() }
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
            Inductive(name) | Constructor(name, _) => self.env.get(name).cloned().ok_or_else(|| format!("Unknown Env item: {}", name)),
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
                Ok(Sort(0)) // 簡化 Universe 檢查
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
                if !is_def_eq(&body_ty, ty, self) { return Err("Fixpoint type mismatch".into()); }
                Ok(*ty.clone())
            }
            Match(_, target, motive, _) => {
                let mut result_ty = App(motive.clone(), target.clone());
                result_ty.whnf(self); Ok(result_ty)
            }
        }
    }
}

fn is_def_eq(e1: &Expr, e2: &Expr, ctx: &Context) -> bool {
    let mut w1 = e1.clone(); w1.whnf(ctx);
    let mut w2 = e2.clone(); w2.whnf(ctx);
    w1 == w2 // 結構比較
}

// ==========================================
// S-Expression Parser (微型 Lean 腳本直譯器)
// ==========================================
#[derive(Clone)] enum SExpr { List(Vec<SExpr>), Atom(String) }

fn parse_sexpr(tokens: &[String], pos: &mut usize) -> SExpr {
    let t = &tokens[*pos]; *pos += 1;
    if t == "(" {
        let mut list = Vec::new();
        while tokens[*pos] != ")" { list.push(parse_sexpr(tokens, pos)); }
        *pos += 1; SExpr::List(list)
    } else { SExpr::Atom(t.clone()) }
}

fn compile(expr: &SExpr, locals: &mut Vec<String>, ctx: &Context) -> Expr {
    match expr {
        SExpr::Atom(s) => {
            if let Some(idx) = locals.iter().rev().position(|x| x == s) { return BVar(idx); }
            if ctx.env.contains_key(s) { return Inductive(s.clone()); }
            if ctx.defs.contains_key(s) { return Const(s.clone()); }
            panic!("Unbound identifier: {}", s);
        }
        SExpr::List(l) => {
            let head = match &l[0] { SExpr::Atom(s) => s.as_str(), _ => panic!("Invalid form") };
            match head {
                "Sort" => Sort(l[1].match_atom().parse().unwrap()),
                "app" => {
                    let mut res = compile(&l[1], locals, ctx);
                    for i in 2..l.len() { res = App(Box::new(res), Box::new(compile(&l[i], locals, ctx))); }
                    res
                }
                "lam" | "pi" | "fix" => {
                    let name = l[1].match_atom();
                    let ty = compile(&l[2], locals, ctx);
                    locals.push(name.clone());
                    let body = compile(&l[3], locals, ctx);
                    locals.pop();
                    match head {
                        "lam" => Lam(Box::new(ty), Box::new(body)),
                        "pi"  => Pi(Box::new(ty), Box::new(body)),
                        "fix" => Fix(Box::new(ty), Box::new(body)),
                        _ => unreachable!(),
                    }
                }
                "let" => {
                    let name = l[1].match_atom();
                    let ty = compile(&l[2], locals, ctx);
                    let val = compile(&l[3], locals, ctx);
                    locals.push(name.clone());
                    let body = compile(&l[4], locals, ctx);
                    locals.pop();
                    Let(Box::new(ty), Box::new(val), Box::new(body))
                }
                "ctor" => Constructor(l[1].match_atom(), l[2].match_atom().parse().unwrap()),
                "match" => {
                    let ind_name = l[1].match_atom();
                    let target = compile(&l[2], locals, ctx);
                    let motive = compile(&l[3], locals, ctx);
                    let branches = l[4..].iter().map(|b| compile(b, locals, ctx)).collect();
                    Match(ind_name, Box::new(target), Box::new(motive), branches)
                }
                _ => panic!("Unknown keyword: {}", head),
            }
        }
    }
}

impl SExpr { fn match_atom(&self) -> String { match self { SExpr::Atom(s) => s.clone(), _ => panic!("Expected atom") } } }

fn run_script(script: &str, ctx: &mut Context) {
    // 修正：先移除所有以 ; 開頭的註解
    let cleaned_script = script.lines()
        .map(|line| {
            if let Some(idx) = line.find(';') {
                &line[..idx]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join(" ");

    let tokens: Vec<String> = cleaned_script.replace("(", " ( ").replace(")", " ) ")
        .split_whitespace().map(|s| s.to_string()).collect();
        
    let mut pos = 0;
    while pos < tokens.len() {
        if let SExpr::List(cmd) = parse_sexpr(&tokens, &mut pos) {
            let kind = cmd[0].match_atom();
            match kind.as_str() {
                "inductive" => {
                    let name = cmd[1].match_atom();
                    let ty = compile(&cmd[2], &mut vec![], ctx);
                    ctx.env.insert(name.clone(), ty); // 註冊本體
                    for (i, c_ty) in cmd[3..].iter().enumerate() {
                        let tag_name = format!("{}.{}", name, i);
                        ctx.env.insert(tag_name, compile(c_ty, &mut vec![], ctx));
                    }
                    println!("=> Defined Inductive: {}", name);
                }
                "def" => {
                    let name = cmd[1].match_atom();
                    let ty = compile(&cmd[2], &mut vec![], ctx);
                    let val = compile(&cmd[3], &mut vec![], ctx);
                    if let Err(e) = ctx.infer_type(&val) {
                        panic!("Type error in def {}: {}", name, e);
                    }
                    ctx.defs.insert(name.clone(), (ty, val));
                    println!("=> Defined: {}", name);
                }
                "check" | "eval" => {
                    let mut expr = compile(&cmd[1], &mut vec![], ctx);
                    if kind == "check" { println!("=> Check: {:?}", ctx.infer_type(&expr).unwrap()); } 
                    else { expr.whnf(ctx); println!("=> Eval: {:?}", expr); }
                }
                _ => panic!("Unknown command"),
            }
        }
    }
}

fn main() {
    let mut ctx = Context::new();

    let bool_lean = r#"
        (inductive Bool (Sort 0)
            Bool     ; ctor 0: true
            Bool)    ; ctor 1: false

        (def not
            (pi b Bool Bool)
            (lam b Bool
                (match Bool b (lam x Bool Bool)
                    (ctor Bool 1)  ; true -> false
                    (ctor Bool 0)  ; false -> true
                )))

        (eval (app not (ctor Bool 0))) ; 測試: not true -> 預期得到 false (ctor Bool 1)
    "#;

    let nat_lean = r#"
        (inductive Nat (Sort 0)
            Nat                  ; 0: zero
            (pi n Nat Nat))      ; 1: succ

        ; let 測試
        (eval (let x Nat (ctor Nat 0) (app (ctor Nat 1) x))) ; 測試: let x = 0 in succ x -> 預期 succ zero

        ; add = fix(add_fn). lam n, m => match n with
        ;   0 => m
        ;   succ n_prev => succ (add_fn n_prev m)
        (def add
            (pi n Nat (pi m Nat Nat))
            (fix add_fn (pi n Nat (pi m Nat Nat))
                (lam n Nat (lam m Nat
                    (match Nat n (lam x Nat Nat)
                        m
                        (lam n_prev Nat (app (ctor Nat 1) (app add_fn n_prev m)))
                    )))))

        ; 測試 1 + 1 (succ zero + succ zero) -> 預期 2 (succ (succ zero))
        (eval (app add 
            (app (ctor Nat 1) (ctor Nat 0)) 
            (app (ctor Nat 1) (ctor Nat 0))))
    "#;

    println!("--- 載入 bool.lean ---");
    run_script(bool_lean, &mut ctx);

    println!("\n--- 載入 nat.lean ---");
    run_script(nat_lean, &mut ctx);
}