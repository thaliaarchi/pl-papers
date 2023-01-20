use Exp::*;
use Val::*;

pub type Int = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp {
    Lit(Int),
    Var(Int),
    Lam(Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    Cons(Box<Exp>, Box<Exp>),
    Let(Box<Exp>, Box<Exp>),
    If(Box<Exp>, Box<Exp>, Box<Exp>),
    IsNum(Box<Exp>),
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

impl Exp {
    // Multi-stage evaluation
    pub fn evalms(self, env: Env) -> Val {
        match self {
            Lit(n) => Cst(n),
            Var(n) => env[n as usize],
            Cons(e1, e2) => Tup(Box::new(e1.evalms(env)), Box::new(e2.evalms(env))),
            Lam(e) => Clo(env, e),
            Let(e1, e2) => {
                env.push(e1.evalms(env));
                e2.evalms(env)
            }
            App(e1, e2) => match (e1.evalms(env), e2.evalms(env)) {
                (Clo(env3, e3), v2) => {
                    env3.push(Clo(env3, e3));
                    e3.evalms(env)
                }
                (Code(s1), Code(s2)) => reflectc(App(s1, s2)),
                _ => panic!(),
            },
        }
    }
}

impl Val {
    // NBE-style polymorphic lift operator
    pub fn lift(&self) -> Exp {
        match *self {
            Cst(n) => Lit(n),
            Tup(a, b) => match (*a, *b) {
                (Code(u), Code(v)) => reflect(Cons(u, v)),
                _ => panic!(),
            },
            Clo(env2, e2) => reflect(Lam(reifyc(evalms(env2)))),
            Code(e) => reflect(Lift(e)),
        }
    }

    pub fn liftc(&self) -> Val {
        Code(Box::new(self.lift()))
    }
}
