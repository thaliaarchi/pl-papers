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
    pub fn lift(&mut self, v: Val) -> Exp {
        match v {
            Cst(n) => Lit(n),
            Tup(a, b) => match (*a, *b) {
                (Code(u), Code(v)) => self.reflect(Cons(u, v)),
                _ => panic!(),
            },
            Clo(mut env2, e2) => {
                env2.push(Code(Box::new(self.fresh())));
                env2.push(Code(Box::new(self.fresh())));
                let e = Box::new(self.reifyc_evalms(&env2, *e2));
                self.reflect(Lam(e))
            }
            Code(e) => self.reflect(Lift(e)),
        }
    }

    pub fn liftc(&mut self, v: Val) -> Val {
        Code(Box::new(self.lift(v)))
    }

    // Multi-stage evaluation
    pub fn evalms(&mut self, env: &Env, e: Exp) -> Val {
        match e {
            Lit(n) => Cst(n),
            Var(n) => env[n as usize].clone(),
            Cons(e1, e2) => Tup(
                Box::new(self.evalms(env, *e1)),
                Box::new(self.evalms(env, *e2)),
            ),
            Lam(e) => Clo(env.clone(), e),
            Let(e1, e2) => {
                let mut env1 = env.clone();
                env1.push(self.evalms(env, *e1));
                self.evalms(&env1, *e2)
            }
            App(e1, e2) => match (self.evalms(env, *e1), self.evalms(env, *e2)) {
                (Code(s1), Code(s2)) => self.reflectc(App(s1, s2)),
                (Clo(env1, s1), v2) => {
                    let mut env3 = env1.clone();
                    env3.push(Clo(env1, s1.clone()));
                    env3.push(v2);
                    self.evalms(&env3, *s1)
                }
                _ => panic!(),
            },
            If(c, a, b) => match self.evalms(env, *c) {
                Code(c1) => {
                    let a2 = Box::new(self.reifyc_evalms(&env, *a));
                    let b2 = Box::new(self.reifyc_evalms(&env, *b));
                    self.reflectc(If(c1, a2, b2))
                }
                Cst(n) => self.evalms(env, *if n != 0 { a } else { b }),
                _ => panic!(),
            },
            IsNum(e) => match self.evalms(env, *e) {
                Code(s) => self.reflectc(IsNum(s)),
                Cst(_) => Cst(1),
                _ => Cst(0),
            },
            IsCons(e) => match self.evalms(env, *e) {
                Code(s) => self.reflectc(IsCons(s)),
                Tup(_, _) => Cst(1),
                _ => Cst(0),
            },
            Car(e) => match self.evalms(env, *e) {
                Code(s) => self.reflectc(Car(s)),
                Tup(a, _) => *a,
                _ => panic!(),
            },
            Cdr(e) => match self.evalms(env, *e) {
                Code(s) => self.reflectc(Cdr(s)),
                Tup(_, b) => *b,
                _ => panic!(),
            },
            Plus(e1, e2) => match (self.evalms(env, *e1), self.evalms(env, *e2)) {
                (Code(s1), Code(s2)) => self.reflectc(Plus(s1, s2)),
                (Cst(n1), Cst(n2)) => Cst(n1 + n2),
                _ => panic!(),
            },
            Minus(e1, e2) => match (self.evalms(env, *e1), self.evalms(env, *e2)) {
                (Code(s1), Code(s2)) => self.reflectc(Minus(s1, s2)),
                (Cst(n1), Cst(n2)) => Cst(n1 - n2),
                _ => panic!(),
            },
            Times(e1, e2) => match (self.evalms(env, *e1), self.evalms(env, *e2)) {
                (Code(s1), Code(s2)) => self.reflectc(Times(s1, s2)),
                (Cst(n1), Cst(n2)) => Cst(n1 * n2),
                _ => panic!(),
            },
            Eq(e1, e2) => match (self.evalms(env, *e1), self.evalms(env, *e2)) {
                (Code(s1), Code(s2)) => self.reflectc(Eq(s1, s2)),
                (Cst(n1), Cst(n2)) => Cst(if n1 == n2 { 1 } else { 0 }),
                _ => panic!(),
            },
            Lift(e) => {
                let v = self.evalms(env, *e);
                self.liftc(v)
            }
            Run(b, e) => match self.evalms(env, *b) {
                Code(b1) => {
                    let e = Box::new(self.reifyc_evalms(env, *e));
                    self.reflectc(Run(b1, e))
                }
                _ => {
                    let e = {
                        let fresh = self.fresh;
                        self.fresh = env.len();
                        let mut block = Vec::new();
                        mem::swap(&mut block, &mut self.block);
                        let e = match self.evalms(env, *e) {
                            Code(e) => *e,
                            _ => panic!(),
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

    fn evalmsg(&mut self, env: &Env, e: Exp) -> Val {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let res = self.evalms(env, e);
        let v = match res {
            Code(last) => Code(Box::new(self.fold_let(*last))),
            _ => panic!(),
        };
        self.fresh = fresh;
        self.block = block;
        v
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

    fn reifyc_evalms(&mut self, env: &Env, e: Exp) -> Exp {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let v = self.evalms(env, e);
        self.fresh = fresh;
        self.block = block;
        self.fold_let(match v {
            Code(e) => *e,
            _ => panic!(),
        })
    }

    fn fold_let(&self, last: Exp) -> Exp {
        let mut e2 = last;
        for e1 in self.block.iter().rev() {
            e2 = Let(Box::new(e1.clone()), Box::new(e2));
        }
        e2
    }
}
