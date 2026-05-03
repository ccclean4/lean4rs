use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// 綁定變數 (Bound Variable)，使用 de Bruijn 索引
    BVar(usize),
    /// 宇宙 (Universes)
    Sort(usize),
    /// 函數應用 (Application)
    App(Box<Expr>, Box<Expr>),
    /// Lambda 抽象 (Lambda Abstraction)
    Lam(Box<Expr>, Box<Expr>),
    /// 依賴函數型別 (Pi Type)
    Pi(Box<Expr>, Box<Expr>),
    
    // --- 新增: 歸納類型相關 ---
    /// 1. 歸納類型 (Inductive)，例如 Nat。儲存其全域名稱。
    Inductive(String),
    /// 2. 建構子 (Constructor)，儲存所屬的歸納類型名稱與索引 (Tag)，例如 (Nat, 0) 代表 zero。
    Constructor(String, usize),
    /// 3. 模式匹配 / 遞迴子 (Match / Recursor)。
    /// 參數依次為：(歸納類型名稱, 目標 target, 動機 motive, 分支 branches)
    Match(String, Box<Expr>, Box<Expr>, Vec<Expr>),
}

use Expr::*;

impl Expr {
    /// 輔助函數：將 f x y 拆解為 (f, [x, y])，用於 iota-reduction 找尋建構子的參數
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
            Sort(_) | Inductive(_) | Constructor(_, _) => {}
            App(f, arg) => {
                f.lift(amount, threshold);
                arg.lift(amount, threshold);
            }
            Lam(ty, body) | Pi(ty, body) => {
                ty.lift(amount, threshold);
                body.lift(amount, threshold + 1);
            }
            Match(_, target, motive, branches) => {
                target.lift(amount, threshold);
                motive.lift(amount, threshold);
                for b in branches {
                    b.lift(amount, threshold);
                }
            }
        }
    }

    fn subst(&mut self, var_idx: usize, value: &Expr) {
        match self {
            BVar(n) => {
                if *n == var_idx {
                    *self = value.clone();
                } else if *n > var_idx {
                    *n -= 1;
                }
            }
            Sort(_) | Inductive(_) | Constructor(_, _) => {}
            App(f, arg) => {
                f.subst(var_idx, value);
                arg.subst(var_idx, value);
            }
            Lam(ty, body) | Pi(ty, body) => {
                ty.subst(var_idx, value);
                let mut shifted_value = value.clone();
                shifted_value.lift(1, 0);
                body.subst(var_idx + 1, &shifted_value);
            }
            Match(_, target, motive, branches) => {
                target.subst(var_idx, value);
                motive.subst(var_idx, value);
                for b in branches {
                    b.subst(var_idx, value);
                }
            }
        }
    }

    /// 弱頭範式 (WHNF) - 執行 Beta-reduction 與 Iota-reduction
    fn whnf(&mut self) {
        let mut new_self = None;

        match self {
            App(f, arg) => {
                f.whnf(); 
                if let Lam(_ty, body) = &**f {
                    // Beta-reduction
                    let mut new_body = *body.clone();
                    new_body.subst(0, arg);
                    new_self = Some(new_body);
                }
            }
            Match(ind_name, target, _motive, branches) => {
                target.whnf(); // 先計算目標
                let (head, args) = target.get_app_fn_args();
                
                // Iota-reduction (ι-reduction)
                // 如果 target 是一個對應的 Constructor，則觸發匹配！
                if let Constructor(c_name, tag) = head {
                    if c_name == ind_name && *tag < branches.len() {
                        // 取出對應的分支
                        let mut res = branches[*tag].clone();
                        // 將 Constructor 的參數依序餵給分支 (App)
                        for arg in args {
                            res = App(Box::new(res), Box::new(arg));
                        }
                        new_self = Some(res);
                    }
                }
            }
            _ => {}
        }

        // 如果發生了化簡，套用新的 Expr 並繼續化簡 (Tail Recursion)
        if let Some(mut ns) = new_self {
            ns.whnf();
            *self = ns;
        }
    }
}

/// 全域的歸納類型定義
#[derive(Clone)]
pub struct InductiveDef {
    pub name: String,
    pub ty: Expr,                // 該歸納類型的型別，例如 Sort(0)
    pub constructors: Vec<Expr>, // 各建構子的型別，例如 Nat 和 Π(n:Nat). Nat
}

pub struct Context {
    types: Vec<Expr>,
    /// 全域環境，儲存所有定義好的歸納類型
    env: HashMap<String, InductiveDef>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            types: Vec::new(),
            env: HashMap::new(),
        }
    }

    pub fn add_inductive(&mut self, def: InductiveDef) {
        self.env.insert(def.name.clone(), def);
    }

    pub fn infer_type(&mut self, expr: &Expr) -> Result<Expr, String> {
        match expr {
            BVar(n) => {
                if *n < self.types.len() {
                    let mut ty = self.types[self.types.len() - 1 - n].clone();
                    ty.lift(*n + 1, 0);
                    Ok(ty)
                } else {
                    Err(format!("Unbound variable: {}", n))
                }
            }
            Sort(u) => Ok(Sort(u + 1)),
            App(f, arg) => {
                let mut f_ty = self.infer_type(f)?;
                f_ty.whnf();
                if let Pi(param_ty, ret_ty) = f_ty {
                    let arg_ty = self.infer_type(arg)?;
                    if !is_def_eq(&arg_ty, &param_ty) {
                        return Err("Type mismatch in application".to_string());
                    }
                    let mut result_ty = *ret_ty.clone();
                    result_ty.subst(0, arg);
                    Ok(result_ty)
                } else {
                    Err("Expected a function type (Pi)".to_string())
                }
            }
            Lam(ty, body) => {
                self.infer_type(ty)?;
                self.types.push(*ty.clone());
                let body_ty = self.infer_type(body)?;
                self.types.pop();
                Ok(Pi(ty.clone(), Box::new(body_ty)))
            }
            Pi(ty, body) => {
                let ty_sort = self.infer_type(ty)?;
                self.types.push(*ty.clone());
                let body_sort = self.infer_type(body)?;
                self.types.pop();
                match (ty_sort, body_sort) {
                    (Sort(_), Sort(u2)) => Ok(Sort(u2)),
                    _ => Err("Invalid Pi type formation".to_string())
                }
            }
            
            // --- 歸納類型型別推導 ---
            Inductive(name) => {
                self.env.get(name)
                    .map(|def| def.ty.clone())
                    .ok_or_else(|| format!("Unknown Inductive type: {}", name))
            }
            Constructor(name, tag) => {
                self.env.get(name)
                    .and_then(|def| def.constructors.get(*tag).cloned())
                    .ok_or_else(|| format!("Unknown Constructor: {}[{}]", name, tag))
            }
            Match(ind_name, target, motive, _branches) => {
                // 1. 檢查目標的型別是否為該歸納類型
                let mut target_ty = self.infer_type(target)?;
                target_ty.whnf();
                let (head, _) = target_ty.get_app_fn_args();
                if let Inductive(n) = head {
                    if n != ind_name {
                        return Err("Target type does not match Match block".to_string());
                    }
                } else {
                    return Err("Target is not an inductive type".to_string());
                }

                // 2. 嚴格 CIC 需檢查 branch 型別，這裡簡化處理
                
                // 3. Match 結構的回傳型別是將目標套用至 motive (Motive Target)
                let mut result_ty = App(motive.clone(), target.clone());
                result_ty.whnf();
                Ok(result_ty)
            }
        }
    }
}

fn is_def_eq(e1: &Expr, e2: &Expr) -> bool {
    let mut e1_whnf = e1.clone();
    let mut e2_whnf = e2.clone();
    e1_whnf.whnf();
    e2_whnf.whnf();
    e1_whnf == e2_whnf
}

fn main() {
    let mut ctx = Context::new();

    // ==========================================
    // 1. 在環境中註冊 Nat (自然數)
    // ==========================================
    let nat_def = InductiveDef {
        name: "Nat".to_string(),
        ty: Sort(0),
        constructors: vec![
            Inductive("Nat".to_string()), // tag 0: zero
            Pi(
                Box::new(Inductive("Nat".to_string())),
                Box::new(Inductive("Nat".to_string()))
            ) // tag 1: succ
        ],
    };
    ctx.add_inductive(nat_def);

    let nat = Inductive("Nat".to_string());
    let zero = Constructor("Nat".to_string(), 0);
    let succ = Constructor("Nat".to_string(), 1);

    // ==========================================
    // 2. 測試：建立數字 1 (succ zero)
    // ==========================================
    let one = App(Box::new(succ.clone()), Box::new(zero.clone()));
    println!("Type of one: {:?}", ctx.infer_type(&one).unwrap());

    // ==========================================
    // 3. 定義 pred (前驅函數) 使用 Match
    // ==========================================
    let motive = Lam(Box::new(nat.clone()), Box::new(nat.clone()));
    
    let branch_zero = zero.clone();
    let branch_succ = Lam(Box::new(nat.clone()), Box::new(BVar(0)));

    let pred = Lam(
        Box::new(nat.clone()),
        Box::new(Match(
            "Nat".to_string(),
            Box::new(BVar(0)), // target 是 n
            Box::new(motive),
            vec![branch_zero, branch_succ]
        ))
    );

    println!("Type of pred: {:?}", ctx.infer_type(&pred).unwrap());

    // ==========================================
    // 4. 計算: pred (succ zero) -> zero
    // ==========================================
    let mut eval_target = App(Box::new(pred), Box::new(one));
    println!("\nBefore Evaluation: {:?}", eval_target);
    
    eval_target.whnf(); // 執行 Beta 與 Iota reduction
    
    println!("After Iota-Reduction (WHNF): {:?}", eval_target);
    assert_eq!(eval_target, zero);
}