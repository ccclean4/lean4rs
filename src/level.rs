#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    UVar(String),
    Param(String),
}

impl Level {
    pub fn of_nat(n: usize) -> Level {
        (0..n).fold(Level::Zero, |l, _| Level::Succ(Box::new(l)))
    }

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

    pub fn to_nat(&self) -> Option<usize> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(l) => l.to_nat().map(|n| n + 1),
            Level::Max(a, b) => {
                let a = a.to_nat()?;
                let b = b.to_nat()?;
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