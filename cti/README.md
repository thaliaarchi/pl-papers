# Collapsing Towers of Interpreters

Implementations of the languages in *Collapsing Towers of Interpreters* using
big- and small-step semantics in Coq and Rust.

- [`BaseFix.v`](BaseFix.v) (Coq): λ⇅ base language implemented as a fixpoint
  with big-step semantics. Adapted from the authors' [`dev-coq`](https://github.com/TiarkRompf/collapsing-towers/blob/master/dev-coq/base.v)
  implementation in Coq.

  - [`Pink.v`](Pink.v): Pink language metacircular interpreter using `BaseFix`.
    Adapted from the [definition in `dev-coq`](https://github.com/TiarkRompf/collapsing-towers/blob/master/dev-coq/base.v#L538-L565),
    which differs somewhat from the [POPL 2018 definition](https://github.com/TiarkRompf/collapsing-towers/blob/master/popl18/pink.scala).

- [`BaseSS.v`](BaseSS.v) (Coq): λ⇅ base language implemented as a relation with
  small-step semantics. Modeled on the small-step definition in the paper.
  Contexts are not yet modeled, though, so it has no separation between between
  `exp` and `val` and is incorrect.

- [`BaseBS.v`](BaseBS.v) (Coq): λ⇅ base language implemented as a relation with
  big-step semantics. Modeled on the big-step definition in the paper.
  Incomplete.

- [`base.rs`](src/base.rs) (Rust): λ⇅ base language implemented with big-step
  semantics. Modeled on the [POPL 2018 Scala artifact](https://github.com/TiarkRompf/collapsing-towers/tree/master/popl18).
