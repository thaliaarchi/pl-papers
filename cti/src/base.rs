use internment::Intern;

use Exp::*;
use Val::*;

pub type Int = i32;
pub type Var = usize;

type ExpRef = Intern<Exp>;
type ValRef = Intern<Val>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Exp {
    Lit(Int),
    Sym(String),
    Cons(ExpRef, ExpRef),
    Lam(ExpRef),

    Var(Var),
    Let(ExpRef, ExpRef),
    If(ExpRef, ExpRef, ExpRef),
    App(ExpRef, ExpRef),
    Op1(Op1Kind, ExpRef),
    Op2(Op2Kind, ExpRef, ExpRef),

    Lift(ExpRef),
    Run(ExpRef, ExpRef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op1Kind {
    IsNum,
    IsStr,
    IsCons,
    Car,
    Cdr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op2Kind {
    Plus,
    Minus,
    Times,
    Eq,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Cst(Int),
    Str(String),
    Tup(ValRef, ValRef),
    Clo(Env, ExpRef),

    Code(ExpRef),
}

pub type Env = Vec<ValRef>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Error {
    Index { index: usize, len: usize },
    Type,
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interpreter {
    fresh: Var,
    block: Vec<ExpRef>,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter::with_fresh(0)
    }

    pub fn with_fresh(fresh: usize) -> Self {
        Interpreter {
            fresh,
            block: Vec::new(),
        }
    }

    // NBE-style polymorphic lift operator
    pub fn lift(&mut self, v: ValRef) -> Result<ExpRef> {
        Ok(match &*v {
            Cst(n) => new_lit(*n),
            Str(s) => new_sym(s.clone()),
            Tup(v1, v2) => self.reflect(new_cons(v1.unwrap_code()?, v2.unwrap_code()?)),
            Clo(env2, e2) => {
                let mut env2 = env2.clone();
                env2.push(new_code(self.fresh()));
                env2.push(new_code(self.fresh()));
                self.reflect(new_lam(self.reifyc_evalms(&env2, *e2)?))
            }
            Code(e) => self.reflect(new_lift(*e)),
        })
    }

    // Multi-stage evaluation
    pub fn evalms(&mut self, env: &Env, e: ExpRef) -> Result<ValRef> {
        Ok(match &*e {
            Lit(n) => new_cst(*n),
            Sym(s) => new_str(s.clone()),
            Cons(e1, e2) => new_tup(self.evalms(env, *e1)?, self.evalms(env, *e2)?),
            Lam(e) => new_clo(env.clone(), *e),
            Var(n) => match env.get(*n) {
                Some(v) => *v,
                None => {
                    return Err(Error::Index {
                        index: *n,
                        len: env.len(),
                    })
                }
            },
            Let(e1, e2) => {
                let mut env1 = env.clone();
                env1.push(self.evalms(env, *e1)?);
                self.evalms(&env1, *e2)?
            }
            If(c, t, f) => match *self.evalms(env, *c)? {
                Code(c1) => {
                    let t2 = self.reifyc_evalms(&env, *t)?;
                    let f2 = self.reifyc_evalms(&env, *f)?;
                    self.reflectc(new_if(c1, t2, f2))
                }
                Cst(n) => self.evalms(env, *if n != 0 { t } else { f })?,
                _ => return Err(Error::Type),
            },
            App(e1, e2) => {
                let v1 = self.evalms(env, *e1)?;
                let v2 = self.evalms(env, *e2)?;
                match (&*v1, &*v2) {
                    (Code(s1), Code(s2)) => self.reflectc(new_app(*s1, *s2)),
                    (Clo(env1, s1), _) => {
                        let mut env3 = env1.clone();
                        env3.push(new_clo(env1.clone(), *s1));
                        env3.push(v2);
                        self.evalms(&env3, *s1)?
                    }
                    _ => return Err(Error::Type),
                }
            }
            Op1(op, e) => match &*self.evalms(env, *e)? {
                Code(e) => self.reflectc(new_op1(*op, *e)),
                v => match op {
                    Op1Kind::IsNum => new_bool(matches!(v, Cst(_))),
                    Op1Kind::IsStr => new_bool(matches!(v, Str(_))),
                    Op1Kind::IsCons => new_bool(matches!(v, Tup(_, _))),
                    Op1Kind::Car => v.unwrap_tup()?.0,
                    Op1Kind::Cdr => v.unwrap_tup()?.1,
                },
            },
            Op2(op, e1, e2) => match (&*self.evalms(env, *e1)?, &*self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => self.reflectc(new_op2(*op, *s1, *s2)),
                (Code(_), _) | (_, Code(_)) => return Err(Error::Type),
                (v1, v2) => {
                    let (n1, n2) = Val::unwrap2_cst(v1, v2)?;
                    match op {
                        Op2Kind::Plus => new_cst(n1 + n2),
                        Op2Kind::Minus => new_cst(n1 - n2),
                        Op2Kind::Times => new_cst(n1 * n2),
                        Op2Kind::Eq => new_bool(n1 == n2),
                    }
                }
            },
            Lift(e) => {
                let v = self.evalms(env, *e)?;
                new_code(self.lift(v)?)
            }
            // First argument decides whether to generate `Run` statement or
            // run code directly.
            Run(c, e) => match *self.evalms(env, *c)? {
                Code(b1) => self.reflectc(new_run(b1, self.reifyc_evalms(env, *e)?)),
                _ => self.evalmsg(env, self.reifyc_evalms_fresh(env, *e, env.len())?)?,
            },
        })
    }

    fn evalmsg(&mut self, env: &Env, e: ExpRef) -> Result<ValRef> {
        Ok(new_code(self.reifyc_evalms(env, e)?))
    }

    fn fresh(&mut self) -> ExpRef {
        self.fresh += 1;
        new_var(self.fresh - 1)
    }

    fn reflect(&mut self, e: ExpRef) -> ExpRef {
        self.block.push(e);
        self.fresh()
    }

    fn reflectc(&mut self, e: ExpRef) -> ValRef {
        new_code(self.reflect(e))
    }

    fn reifyc_evalms(&self, env: &Env, e: ExpRef) -> Result<ExpRef> {
        self.reifyc_evalms_fresh(env, e, self.fresh)
    }

    fn reifyc_evalms_fresh(&self, env: &Env, e: ExpRef, fresh: usize) -> Result<ExpRef> {
        let v = Interpreter::with_fresh(fresh).evalms(env, e)?;
        Ok(self.fold_let(v.unwrap_code()?))
    }

    fn fold_let(&self, last: ExpRef) -> ExpRef {
        let mut e2 = last;
        for &e1 in self.block.iter().rev() {
            e2 = new_let(e1, e2);
        }
        e2
    }
}

impl Val {
    #[inline]
    pub fn unwrap_cst(&self) -> Result<Int> {
        match self {
            Cst(n) => Ok(*n),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_str(&self) -> Result<&String> {
        match self {
            Str(s) => Ok(s),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_tup(&self) -> Result<(ValRef, ValRef)> {
        match self {
            Tup(a, b) => Ok((*a, *b)),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_clo(&self) -> Result<(&Env, ExpRef)> {
        match self {
            Clo(env, e) => Ok((env, *e)),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_code(&self) -> Result<ExpRef> {
        match self {
            Code(e) => Ok(*e),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap2_cst(v1: &Val, v2: &Val) -> Result<(Int, Int)> {
        Ok((v1.unwrap_cst()?, v2.unwrap_cst()?))
    }

    #[inline]
    pub fn unwrap2_code(v1: &Val, v2: &Val) -> Result<(ExpRef, ExpRef)> {
        Ok((v1.unwrap_code()?, v2.unwrap_code()?))
    }
}

pub fn new_lit(n: Int) -> ExpRef {
    Intern::new(Exp::Lit(n))
}
pub fn new_sym(s: String) -> ExpRef {
    Intern::new(Exp::Sym(s))
}
pub fn new_cons(e1: ExpRef, e2: ExpRef) -> ExpRef {
    Intern::new(Exp::Cons(e1, e2))
}
pub fn new_lam(e: ExpRef) -> ExpRef {
    Intern::new(Exp::Lam(e))
}
pub fn new_var(n: Var) -> ExpRef {
    Intern::new(Exp::Var(n))
}
pub fn new_let(e1: ExpRef, e2: ExpRef) -> ExpRef {
    Intern::new(Exp::Let(e1, e2))
}
pub fn new_if(c: ExpRef, a: ExpRef, b: ExpRef) -> ExpRef {
    Intern::new(Exp::If(c, a, b))
}
pub fn new_app(e1: ExpRef, e2: ExpRef) -> ExpRef {
    Intern::new(Exp::App(e1, e2))
}
pub fn new_op1(op: Op1Kind, e: ExpRef) -> ExpRef {
    Intern::new(Exp::Op1(op, e))
}
pub fn new_op2(op: Op2Kind, e1: ExpRef, e2: ExpRef) -> ExpRef {
    Intern::new(Exp::Op2(op, e1, e2))
}
pub fn new_lift(e: ExpRef) -> ExpRef {
    Intern::new(Exp::Lift(e))
}
pub fn new_run(b: ExpRef, e: ExpRef) -> ExpRef {
    Intern::new(Exp::Run(b, e))
}

pub fn new_is_num(e: ExpRef) -> ExpRef {
    new_op1(Op1Kind::IsNum, e)
}
pub fn new_is_str(e: ExpRef) -> ExpRef {
    new_op1(Op1Kind::IsStr, e)
}
pub fn new_is_cons(e: ExpRef) -> ExpRef {
    new_op1(Op1Kind::IsCons, e)
}
pub fn new_car(e: ExpRef) -> ExpRef {
    new_op1(Op1Kind::Car, e)
}
pub fn new_cdr(e: ExpRef) -> ExpRef {
    new_op1(Op1Kind::Cdr, e)
}

pub fn new_plus(e1: ExpRef, e2: ExpRef) -> ExpRef {
    new_op2(Op2Kind::Plus, e1, e2)
}
pub fn new_minus(e1: ExpRef, e2: ExpRef) -> ExpRef {
    new_op2(Op2Kind::Minus, e1, e2)
}
pub fn new_times(e1: ExpRef, e2: ExpRef) -> ExpRef {
    new_op2(Op2Kind::Times, e1, e2)
}
pub fn new_eq(e1: ExpRef, e2: ExpRef) -> ExpRef {
    new_op2(Op2Kind::Eq, e1, e2)
}

pub fn new_cst(n: Int) -> ValRef {
    Intern::new(Val::Cst(n))
}
pub fn new_str(s: String) -> ValRef {
    Intern::new(Val::Str(s))
}
pub fn new_tup(a: ValRef, b: ValRef) -> ValRef {
    Intern::new(Val::Tup(a, b))
}
pub fn new_clo(env: Env, e: ExpRef) -> ValRef {
    Intern::new(Val::Clo(env, e))
}
pub fn new_code(e: ExpRef) -> ValRef {
    Intern::new(Val::Code(e))
}

pub fn new_bool(b: bool) -> ValRef {
    new_cst(if b { 1 } else { 0 })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test from POPL 2018 Scala artifact:
    // https://github.com/TiarkRompf/collapsing-towers/blob/master/popl18/base.scala#L330-L364
    #[test]
    fn staged_factorial() {
        /*
          Pattern:
            def f = fun { n => if (n != 0) f(n-1) else 1 }
          Corresponds to:
            val f = { () => lift({ n => if (n != 0) f()(n-1) else 1 }) }
        */
        let f_self = new_app(new_var(0), new_lit(99));
        let n = new_var(3);

        let fac_body = new_lam(new_if(
            n,
            new_times(n, new_app(f_self, new_minus(n, new_lift(new_lit(1))))),
            new_lift(new_lit(1)),
        ));
        let fac = new_app(new_lam(new_lift(fac_body)), new_lit(99));

        let out = new_let(
            new_lam(new_let(
                new_if(
                    new_var(1),
                    new_let(
                        new_minus(new_var(1), new_lit(1)),
                        new_let(
                            new_app(new_var(0), new_var(2)),
                            new_let(new_times(new_var(1), new_var(3)), new_var(4)),
                        ),
                    ),
                    new_lit(1),
                ),
                new_var(2),
            )),
            new_var(0),
        );

        let code = Interpreter::new().reifyc_evalms(&Vec::new(), fac).unwrap();
        assert_eq!(out, code);

        let res = Interpreter::new()
            .reifyc_evalms(&Vec::new(), new_app(code, new_lit(4)))
            .unwrap();
        assert_eq!(new_lit(4), res);
    }
}
