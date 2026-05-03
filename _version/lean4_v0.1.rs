#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// 綁定變數 (Bound Variable)，使用 de Bruijn 索引
    BVar(usize),
    /// 宇宙 (Universes)，例如 Sort(0) 相當於 Prop，Sort(1) 相當於 Type
    Sort(usize),
    /// 函數應用 (Application): f x
    App(Box<Expr>, Box<Expr>),
    /// Lambda 抽象 (Lambda Abstraction): λ (x : A). b
    /// 這裡我們儲存參數型別 (A) 與主體 (b)
    Lam(Box<Expr>, Box<Expr>),
    /// 依賴函數型別 (Pi Type): Π (x : A). B
    Pi(Box<Expr>, Box<Expr>),
}

use Expr::*;

impl Expr {
    /// 簡單的變數提升 (Lift) - 用於 de Bruijn 索引調整
    fn lift(&mut self, amount: usize, threshold: usize) {
        match self {
            BVar(n) => {
                if *n >= threshold {
                    *n += amount;
                }
            }
            Sort(_) => {}
            App(f, arg) => {
                f.lift(amount, threshold);
                arg.lift(amount, threshold);
            }
            Lam(ty, body) | Pi(ty, body) => {
                ty.lift(amount, threshold);
                // 進入 body 時，threshold 加 1，因為多了一層綁定
                body.lift(amount, threshold + 1);
            }
        }
    }

    /// 將索引為 `var_idx` 的 BVar 替換為 `value`
    fn subst(&mut self, var_idx: usize, value: &Expr) {
        match self {
            BVar(n) => {
                if *n == var_idx {
                    *self = value.clone();
                } else if *n > var_idx {
                    *n -= 1; // 自由變數下降
                }
            }
            Sort(_) => {}
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
        }
    }

    /// 弱頭範式 (Weak Head Normal Form) - 執行運算 (beta-reduction)
    fn whnf(&mut self) {
        if let App(f, arg) = self {
            f.whnf(); // 先化簡函數部分
            if let Lam(_ty, body) = &**f {
                // 如果 f 是一個 Lambda，執行 beta-reduction: (λx. body) arg -> body[x := arg]
                let mut new_body = *body.clone();
                new_body.subst(0, arg);
                *self = new_body;
                self.whnf(); // 繼續化簡
            }
        }
    }
}

/// 型別檢查器環境 (Context)
pub struct Context {
    /// 儲存局部變數的型別
    types: Vec<Expr>,
}

impl Context {
    pub fn new() -> Self {
        Context { types: Vec::new() }
    }

    /// 核心推導函數：給定一個表達式，推導出它的型別
    pub fn infer_type(&mut self, expr: &Expr) -> Result<Expr, String> {
        match expr {
            // 變數的型別從 Context 中查找
            BVar(n) => {
                if *n < self.types.len() {
                    // 取出型別並根據深度提升索引
                    let mut ty = self.types[self.types.len() - 1 - n].clone();
                    ty.lift(*n + 1, 0);
                    Ok(ty)
                } else {
                    Err(format!("Unbound variable: {}", n))
                }
            }
            
            // 公理：Sort(u) 的型別是 Sort(u+1)
            Sort(u) => Ok(Sort(u + 1)),

            // Application (f x) 的型別檢查
            App(f, arg) => {
                let mut f_ty = self.infer_type(f)?;
                f_ty.whnf(); // 化簡 f 的型別
                
                // f 的型別必須是 Pi (Π)
                if let Pi(param_ty, ret_ty) = f_ty {
                    let arg_ty = self.infer_type(arg)?;
                    
                    // 檢查傳入的參數型別是否符合
                    if !is_def_eq(&arg_ty, &param_ty) {
                        return Err("Type mismatch in application".to_string());
                    }
                    
                    // 回傳型別：替換依賴型別中的變數 B[x := arg]
                    let mut result_ty = *ret_ty.clone();
                    result_ty.subst(0, arg);
                    Ok(result_ty)
                } else {
                    Err("Expected a function type (Pi)".to_string())
                }
            }

            // Lambda 抽象的型別推導：λ(x:A).b 的型別是 Π(x:A).B
            Lam(ty, body) => {
                // 先檢查參數型別 A 是否為合法的 Sort
                self.infer_type(ty)?;
                
                // 將 A 加入 Context，推導 body 的型別 B
                self.types.push(*ty.clone());
                let body_ty = self.infer_type(body)?;
                self.types.pop();
                
                Ok(Pi(ty.clone(), Box::new(body_ty)))
            }

            // Pi 型別的形成規則
            Pi(ty, body) => {
                let ty_sort = self.infer_type(ty)?;
                self.types.push(*ty.clone());
                let body_sort = self.infer_type(body)?;
                self.types.pop();
                
                // 在標準 CIC 中，Pi 規則會根據 ty_sort 和 body_sort 的宇宙層級計算出新的層級
                // 這裡簡化為回傳 body 的 Sort (Impredicativity of Prop 的簡化版)
                match (ty_sort, body_sort) {
                    (Sort(_), Sort(u2)) => Ok(Sort(u2)),
                    _ => Err("Invalid Pi type formation".to_string())
                }
            }
        }
    }
}

/// 定義相等性檢查 (Definitional Equality)
fn is_def_eq(e1: &Expr, e2: &Expr) -> bool {
    let mut e1_whnf = e1.clone();
    let mut e2_whnf = e2.clone();
    e1_whnf.whnf();
    e2_whnf.whnf();
    
    // 這裡應該做深層的結構比較，為求簡潔，直接用 Rust 的 PartialEq 比較展開後的結果
    e1_whnf == e2_whnf
}

fn main() {
    let mut ctx = Context::new();

    // 測試：建構一個恆等函數 id = λ(A: Sort(0)). λ(a: A). a
    let type_0 = Box::new(Sort(0));
    let id_func = Lam(
        type_0.clone(), // 參數 1 型別: A : Type(0)
        Box::new(Lam(
            Box::new(BVar(0)), // 參數 2 型別: a : A (此時 A 是 BVar(0))
            Box::new(BVar(0))  // 回傳 a (此時 a 是 BVar(0))
        ))
    );

    match ctx.infer_type(&id_func) {
        Ok(ty) => println!("推導成功！型別為: {:?}", ty),
        Err(e) => println!("型別錯誤: {}", e),
    }
}