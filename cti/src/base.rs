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
    IsNum(Box<Exp>),
    IsCons(Box<Exp>),
    Car(Box<Exp>),
    Cdr(Box<Exp>),
    Plus(Box<Exp>, Box<Exp>),
    Minus(Box<Exp>, Box<Exp>),
    Times(Box<Exp>, Box<Exp>),
    Eq(Box<Exp>, Box<Exp>),
    Lift(Box<Exp>),
    Run(Box<Exp>, Box<Exp>),
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
    pub fn lift(&mut self, v: Val) -> Result<Exp> {
        match v {
            Cst(n) => Ok(Lit(n)),
            Tup(a, b) => match (*a, *b) {
                (Code(u), Code(v)) => Ok(self.reflect(Cons(u, v))),
                _ => Err(Error::Type),
            },
            Clo(mut env2, e2) => {
                env2.push(Code(Box::new(self.fresh())));
                env2.push(Code(Box::new(self.fresh())));
                let e = Box::new(self.reifyc_evalms(&env2, *e2)?);
                Ok(self.reflect(Lam(e)))
            }
            Code(e) => Ok(self.reflect(Lift(e))),
        }
    }

    pub fn liftc(&mut self, v: Val) -> Result<Val> {
        Ok(Code(Box::new(self.lift(v)?)))
    }

    // Multi-stage evaluation
    pub fn evalms(&mut self, env: &Env, e: Exp) -> Result<Val> {
        match e {
            Lit(n) => Ok(Cst(n)),
            Var(n) => match env.get(n as usize) {
                Some(v) => Ok(v.clone()),
                None => Err(Error::Index {
                    index: n,
                    len: env.len(),
                }),
            },
            Cons(e1, e2) => Ok(Tup(
                Box::new(self.evalms(env, *e1)?),
                Box::new(self.evalms(env, *e2)?),
            )),
            Lam(e) => Ok(Clo(env.clone(), e)),
            Let(e1, e2) => {
                let mut env1 = env.clone();
                env1.push(self.evalms(env, *e1)?);
                self.evalms(&env1, *e2)
            }
            App(e1, e2) => match (self.evalms(env, *e1)?, self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(App(s1, s2))),
                (Clo(env1, s1), v2) => {
                    let mut env3 = env1.clone();
                    env3.push(Clo(env1, s1.clone()));
                    env3.push(v2);
                    self.evalms(&env3, *s1)
                }
                _ => Err(Error::Type),
            },
            If(c, a, b) => match self.evalms(env, *c)? {
                Code(c1) => {
                    let a2 = Box::new(self.reifyc_evalms(&env, *a)?);
                    let b2 = Box::new(self.reifyc_evalms(&env, *b)?);
                    Ok(self.reflectc(If(c1, a2, b2)))
                }
                Cst(n) => self.evalms(env, *if n != 0 { a } else { b }),
                _ => Err(Error::Type),
            },
            IsNum(e) => match self.evalms(env, *e)? {
                Code(s) => Ok(self.reflectc(IsNum(s))),
                Cst(_) => Ok(Cst(1)),
                _ => Ok(Cst(0)),
            },
            IsCons(e) => match self.evalms(env, *e)? {
                Code(s) => Ok(self.reflectc(IsCons(s))),
                Tup(_, _) => Ok(Cst(1)),
                _ => Ok(Cst(0)),
            },
            Car(e) => match self.evalms(env, *e)? {
                Code(s) => Ok(self.reflectc(Car(s))),
                Tup(a, _) => Ok(*a),
                _ => Err(Error::Type),
            },
            Cdr(e) => match self.evalms(env, *e)? {
                Code(s) => Ok(self.reflectc(Cdr(s))),
                Tup(_, b) => Ok(*b),
                _ => Err(Error::Type),
            },
            Plus(e1, e2) => match (self.evalms(env, *e1)?, self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(Plus(s1, s2))),
                (Cst(n1), Cst(n2)) => Ok(Cst(n1 + n2)),
                _ => Err(Error::Type),
            },
            Minus(e1, e2) => match (self.evalms(env, *e1)?, self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(Minus(s1, s2))),
                (Cst(n1), Cst(n2)) => Ok(Cst(n1 - n2)),
                _ => Err(Error::Type),
            },
            Times(e1, e2) => match (self.evalms(env, *e1)?, self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(Times(s1, s2))),
                (Cst(n1), Cst(n2)) => Ok(Cst(n1 * n2)),
                _ => Err(Error::Type),
            },
            Eq(e1, e2) => match (self.evalms(env, *e1)?, self.evalms(env, *e2)?) {
                (Code(s1), Code(s2)) => Ok(self.reflectc(Eq(s1, s2))),
                (Cst(n1), Cst(n2)) => Ok(Cst(if n1 == n2 { 1 } else { 0 })),
                _ => Err(Error::Type),
            },
            Lift(e) => {
                let v = self.evalms(env, *e)?;
                self.liftc(v)
            }
            Run(b, e) => match self.evalms(env, *b)? {
                Code(b1) => {
                    let e = Box::new(self.reifyc_evalms(env, *e)?);
                    Ok(self.reflectc(Run(b1, e)))
                }
                _ => {
                    let e = {
                        let fresh = self.fresh;
                        self.fresh = env.len();
                        let mut block = Vec::new();
                        mem::swap(&mut block, &mut self.block);
                        let e = match self.evalms(env, *e)? {
                            Code(e) => *e,
                            _ => return Err(Error::Type),
                        };
                        self.fresh = fresh;
                        self.block = block;
                        self.fold_let(e)
                    };
                    self.evalmsg(env, e)
                }
            },
        }
    }

    fn evalmsg(&mut self, env: &Env, e: Exp) -> Result<Val> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let res = self.evalms(env, e)?;
        self.fresh = fresh;
        self.block = block;
        match res {
            Code(last) => Ok(Code(Box::new(self.fold_let(*last)))),
            _ => Err(Error::Type),
        }
    }

    fn fresh(&mut self) -> Exp {
        self.fresh += 1;
        Var(self.fresh - 1)
    }

    fn reflect(&mut self, s: Exp) -> Exp {
        self.block.push(s);
        self.fresh()
    }

    fn reflectc(&mut self, s: Exp) -> Val {
        Code(Box::new(self.reflect(s)))
    }

    fn reifyc_evalms(&mut self, env: &Env, e: Exp) -> Result<Exp> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let v = self.evalms(env, e)?;
        self.fresh = fresh;
        self.block = block;
        Ok(self.fold_let(match v {
            Code(e) => *e,
            _ => return Err(Error::Type),
        }))
    }

    fn fold_let(&self, last: Exp) -> Exp {
        let mut e2 = last;
        for e1 in self.block.iter().rev() {
            e2 = Let(Box::new(e1.clone()), Box::new(e2));
        }
        e2
    }
}
