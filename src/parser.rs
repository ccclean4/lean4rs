use crate::elaborator::{PreExpr, PreLevel};
use crate::expr::BinderInfo;

struct Parser {
    tokens: Vec<String>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&str> { self.tokens.get(self.pos).map(|s| s.as_str()) }
    fn peek_nth(&self, n: usize) -> Option<&str> { self.tokens.get(self.pos + n).map(|s| s.as_str()) }
    fn next_tok(&mut self) -> String {
        let t = self.tokens[self.pos].clone();
        self.pos += 1;
        t
    }
    fn consume(&mut self, expected: &str) {
        let t = self.next_tok();
        if t != expected { panic!("Expected '{}', got '{}'", expected, t); }
    }
    fn eof(&self) -> bool { self.pos >= self.tokens.len() }
    fn at(&self, s: &str) -> bool { self.peek() == Some(s) }
}

fn read_ident(p: &mut Parser) -> String {
    let first = p.next_tok();
    let mut name = first;
    while p.at(".") {
        p.pos += 1;
        if let Some(next) = p.peek() {
            if next == "{" || next == "[" || next == "(" || is_terminator(next) {
                p.pos -= 1;
                break;
            }
            if next == "." {
                if let Some(after_dot) = p.peek_nth(1) {
                    if after_dot == "{" || after_dot == "[" || after_dot == "(" || is_terminator(after_dot) {
                        p.pos -= 1;
                        break;
                    }
                }
            }
        }
        name.push('.');
        name.push_str(&p.next_tok());
    }
    name
}

fn is_terminator(t: &str) -> bool {
    matches!(t, ")" | "}" | "]" | "->" | "→" | "=>" | ":=" | ";"
        | "," | "|" | "with" | "return" | "where" | "def" | "inductive"
        | "#eval" | "#check" | "universe")
}

pub fn tokenize(src: &str) -> Vec<String> {
    let cleaned = src.lines()
        .map(|line| if let Some(i) = line.find("--") { &line[..i] } else { line })
        .collect::<Vec<_>>().join(" ");

    let mut out = String::new();
    let chars: Vec<char> = cleaned.chars().collect();
    let mut i = 0;
    while i < chars.len() {
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
            '.' => {
                if i + 1 < chars.len() && (chars[i+1] == '{' || chars[i+1] == '[' || chars[i+1] == '(') {
                    out.push_str(" . ");
                } else {
                    out.push('.');
                }
            }
            c => out.push(c),
        }
        i += 1;
    }
    out.split_whitespace().map(|s| s.to_string()).collect()
}

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

fn try_parse_binder(p: &mut Parser) -> Option<(BinderInfo, String, PreExpr)> {
    let (bi, _open, close) = match p.peek()? {
        "(" => (BinderInfo::Default, "(", ")"),
        "{" => (BinderInfo::Implicit, "{", "}"),
        "[" => (BinderInfo::Instance, "[", "]"),
        _ => return None,
    };
    let saved = p.pos;
    p.pos += 1;
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
    if let Some((bi, name, ty)) = try_parse_binder(p) {
        if p.at("->") || p.at("→") {
            p.pos += 1;
            let body = parse_arrow(p);
            return PreExpr::Pi(bi, name, Box::new(ty), Box::new(body));
        }
        return ty;
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
            binders.into_iter().rev().fold(body, |acc, (bi, name, ty)| {
                PreExpr::Lam(bi, name, Box::new(ty), Box::new(acc))
            })
        }
        Some("fix") => {
            p.consume("fix");
            let fname = read_ident(p);
            p.consume(":");
            let ty = parse_expr(p);
            p.consume("=>");
            let body = parse_expr(p);
            PreExpr::Fix(fname, Box::new(ty), Box::new(body))
        }
        Some("let") => {
            p.consume("let");
            let name = read_ident(p);
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
            let motive = if p.at("return") {
                p.consume("return");
                Some(Box::new(parse_expr(p)))
            } else { None };
            p.consume("with");
            let mut branches = Vec::new();
            while !p.eof() && p.at("|") {
                p.consume("|");
                let ctor_name = read_ident(p);
                let mut binder_names = Vec::new();
                while !p.at("=>") {
                    binder_names.push(p.next_tok());
                }
                p.consume("=>");
                let body = parse_expr(p);
                branches.push((ctor_name, binder_names, Box::new(body)));
            }
            let ind_name = if !branches.is_empty() {
                branches[0].0.split('.').next().unwrap_or("").to_string()
            } else { "".to_string() };
            PreExpr::Match(ind_name, Box::new(target), motive, branches)
        }
        _ => parse_arrow(p),
    }
}

pub fn run_script(script: &str, elab: &mut crate::elaborator::Elaborator) {
    let tokens = tokenize(script);
    let mut p = Parser { tokens, pos: 0 };

    while !p.eof() {
        match p.next_tok().as_str() {
            "inductive" => {
                let name = read_ident(&mut p);
                if p.at(".") && p.peek_nth(1) == Some("{") { p.pos += 1; }
                let uparams = if p.at("{") {
                    p.consume("{");
                    let mut ps = Vec::new();
                    while !p.at("}") { ps.push(p.next_tok()); }
                    p.consume("}");
                    ps
                } else { vec![] };
                p.consume(":");
                let ty_pre = parse_expr(&mut p);
                let ty = elab.elab(&ty_pre, None, &uparams).unwrap();
                elab.env.inductives.insert(name.clone(), (uparams.clone(), ty));

                if p.at("where") { p.pos += 1; }

                let mut tag = 0;
                while !p.eof() && p.at("|") {
                    p.consume("|");
                    let ctor_name = read_ident(&mut p);
                    p.consume(":");
                    let ctor_ty_pre = parse_expr(&mut p);
                    let ctor_ty = elab.elab(&ctor_ty_pre, None, &uparams).unwrap();
                    elab.env.ctors.insert(
                        ctor_name.clone(),
                        (name.clone(), tag, uparams.clone(), ctor_ty.clone()),
                    );
                    tag += 1;
                }
                println!("=> Defined inductive: {}", name);
            }
            "def" => {
                let name = read_ident(&mut p);
                eprintln!("DEBUG def: name='{}' at='{:?}' peek='{:?}'", name, p.peek(), p.peek_nth(1));
                if p.at(".") && p.peek_nth(1) == Some("{") { p.pos += 1; }
                eprintln!("DEBUG def after skip: at='{:?}' peek='{:?}'", p.peek(), p.peek_nth(1));
                let uparams = if p.at("{") {
                    p.consume("{");
                    let mut ps = Vec::new();
                    while !p.at("}") { ps.push(p.next_tok()); }
                    p.consume("}");
                    ps
                } else { vec![] };
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
                        crate::kernel::Kernel::new(&elab.env).nf(&mut expr);
                        println!("=> {}", crate::kernel::pretty_expr(&expr, &elab.env));
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
                        let ty = crate::kernel::Kernel::new(&elab.env).infer(&expr, &mut crate::kernel::LocalCtx::new()).unwrap_or_else(|_| crate::expr::Expr::Sort(crate::level::Level::Zero));
                        println!("=> {} : {}", crate::kernel::pretty_expr(&expr, &elab.env), crate::kernel::pretty_expr(&ty, &elab.env));
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            t => panic!("Unknown top-level token: {}", t),
        }
    }
}