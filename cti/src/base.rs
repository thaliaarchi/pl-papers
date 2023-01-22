use std::mem;

use Exp::*;
use Val::*;

pub type Int = u32;
pub type Var = usize;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp {
    Lit(Int),
    Var(Var),
    Lam(Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    Cons(Box<Exp>, Box<Exp>),
    Let(Box<Exp>, Box<Exp>),
    If(Box<Exp>, Box<Exp>, Box<Exp>),
    Op1(Op1Kind, Box<Exp>),
    Op2(Op2Kind, Box<Exp>, Box<Exp>),
    Lift(Box<Exp>),
    Run(Box<Exp>, Box<Exp>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op1Kind {
    IsNum,
    IsCons,
    Car,
    Cdr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op2Kind {
    Plus,
    Minus,
    Times,
    Eq,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Cst(Int),
    Tup(Box<Val>, Box<Val>),
    Clo(Env, Box<Exp>),
    Code(Box<Exp>),
}

pub type Env = Vec<Val>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Index { index: usize, len: usize },
    Type,
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interpreter {
    fresh: Var,
    block: Vec<Exp>,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            fresh: 0,
            block: Vec::new(),
        }
    }

    // NBE-style polymorphic lift operator
    pub fn lift(&mut self, v: Box<Val>) -> Result<Box<Exp>> {
        match *v {
            Cst(n) => Ok(Box::new(Lit(n))),
            Tup(a, b) => Ok(self.reflect(Cons(a.unwrap_code()?, b.unwrap_code()?))),
            Clo(mut env2, e2) => {
                env2.push(Code(self.fresh()));
                env2.push(Code(self.fresh()));
                let e = self.reifyc_evalms(&env2, e2)?;
                Ok(self.reflect(Lam(e)))
            }
            Code(e) => Ok(self.reflect(Lift(e))),
        }
    }

    pub fn liftc(&mut self, v: Box<Val>) -> Result<Box<Val>> {
        Ok(Box::new(Code(self.lift(v)?)))
    }

    // Multi-stage evaluation
    pub fn evalms(&mut self, env: &Env, e: Box<Exp>) -> Result<Box<Val>> {
        match *e {
            Lit(n) => Ok(Box::new(Cst(n))),
            Var(n) => match env.get(n as usize) {
                Some(v) => Ok(Box::new(v.clone())),
                None => Err(Error::Index {
                    index: n,
                    len: env.len(),
                }),
            },
            Cons(e1, e2) => Ok(Box::new(Tup(self.evalms(env, e1)?, self.evalms(env, e2)?))),
            Lam(e) => Ok(Box::new(Clo(env.clone(), e))),
            Let(e1, e2) => {
                let mut env1 = env.clone();
                env1.push(*self.evalms(env, e1)?);
                self.evalms(&env1, e2)
            }
            App(e1, e2) => match (*self.evalms(env, e1)?, *self.evalms(env, e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(App(s1, s2))),
                (Clo(env1, s1), v2) => {
                    let mut env3 = env1.clone();
                    env3.push(Clo(env1, s1.clone()));
                    env3.push(v2);
                    self.evalms(&env3, s1)
                }
                _ => Err(Error::Type),
            },
            If(c, a, b) => match *self.evalms(env, c)? {
                Code(c1) => {
                    let a2 = self.reifyc_evalms(&env, a)?;
                    let b2 = self.reifyc_evalms(&env, b)?;
                    Ok(self.reflectc(If(c1, a2, b2)))
                }
                Cst(n) => self.evalms(env, if n != 0 { a } else { b }),
                _ => Err(Error::Type),
            },
            Op1(op, e) => match *self.evalms(env, e)? {
                Code(s) => Ok(self.reflectc(Op1(op, s))),
                v => match op {
                    Op1Kind::IsNum => Ok(Val::bool(matches!(v, Cst(_)))),
                    Op1Kind::IsCons => Ok(Val::bool(matches!(v, Tup(_, _)))),
                    Op1Kind::Car => Ok(v.unwrap_tup()?.0),
                    Op1Kind::Cdr => Ok(v.unwrap_tup()?.1),
                },
            },
            Op2(op, e1, e2) => match (*self.evalms(env, e1)?, *self.evalms(env, e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(Op2(op, s1, s2))),
                (Code(_), _) | (_, Code(_)) => Err(Error::Type),
                (v1, v2) => {
                    let (n1, n2) = Val::unwrap2_cst(v1, v2)?;
                    match op {
                        Op2Kind::Plus => Ok(Box::new(Cst(n1 + n2))),
                        Op2Kind::Minus => Ok(Box::new(Cst(n1 - n2))),
                        Op2Kind::Times => Ok(Box::new(Cst(n1 * n2))),
                        Op2Kind::Eq => Ok(Val::bool(n1 == n2)),
                    }
                }
            },
            Lift(e) => {
                let v = self.evalms(env, e)?;
                self.liftc(v)
            }
            Run(b, e) => match *self.evalms(env, b)? {
                Code(b1) => {
                    let e = self.reifyc_evalms(env, e)?;
                    Ok(self.reflectc(Run(b1, e)))
                }
                _ => {
                    let e = {
                        let fresh = self.fresh;
                        self.fresh = env.len();
                        let mut block = Vec::new();
                        mem::swap(&mut block, &mut self.block);
                        let e = self.evalms(env, e)?.unwrap_code()?;
                        self.fresh = fresh;
                        self.block = block;
                        self.fold_let(e)
                    };
                    self.evalmsg(env, e)
                }
            },
        }
    }

    fn evalmsg(&mut self, env: &Env, e: Box<Exp>) -> Result<Box<Val>> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let last = self.evalms(env, e)?.unwrap_code()?;
        self.fresh = fresh;
        self.block = block;
        Ok(Box::new(Code(self.fold_let(last))))
    }

    fn fresh(&mut self) -> Box<Exp> {
        self.fresh += 1;
        Box::new(Var(self.fresh - 1))
    }

    fn reflect(&mut self, s: Exp) -> Box<Exp> {
        self.block.push(s);
        self.fresh()
    }

    fn reflectc(&mut self, s: Exp) -> Box<Val> {
        Box::new(Code(self.reflect(s)))
    }

    fn reifyc_evalms(&mut self, env: &Env, e: Box<Exp>) -> Result<Box<Exp>> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let v = self.evalms(env, e)?;
        self.fresh = fresh;
        self.block = block;
        Ok(self.fold_let(v.unwrap_code()?))
    }

    fn fold_let(&self, last: Box<Exp>) -> Box<Exp> {
        let mut e2 = last;
        for e1 in self.block.iter().rev() {
            e2 = Box::new(Let(Box::new(e1.clone()), e2));
        }
        e2
    }
}

impl Val {
    #[inline]
    pub fn bool(value: bool) -> Box<Val> {
        Box::new(Cst(if value { 1 } else { 0 }))
    }

    #[inline]
    pub fn unwrap_cst(self) -> Result<Int> {
        match self {
            Cst(n) => Ok(n),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_tup(self) -> Result<(Box<Val>, Box<Val>)> {
        match self {
            Tup(a, b) => Ok((a, b)),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_clo(self) -> Result<(Env, Box<Exp>)> {
        match self {
            Clo(env, e) => Ok((env, e)),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap_code(self) -> Result<Box<Exp>> {
        match self {
            Code(e) => Ok(e),
            _ => Err(Error::Type),
        }
    }

    #[inline]
    pub fn unwrap2_cst(v1: Val, v2: Val) -> Result<(Int, Int)> {
        Ok((v1.unwrap_cst()?, v2.unwrap_cst()?))
    }

    #[inline]
    pub fn unwrap2_code(v1: Val, v2: Val) -> Result<(Box<Exp>, Box<Exp>)> {
        Ok((v1.unwrap_code()?, v2.unwrap_code()?))
    }
}
