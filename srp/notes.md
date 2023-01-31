# An Array-Oriented Language with Static Rank Polymorphism

## Dependent types

> §1.1 *Decidability* Despite its expressive power, the dependent elements of
> Remora’s type system are constrained to make the type-checking problem
> decidable.

Is Coq's dependent type system also constrained? No?

> §2.2 Xi’s Dependent ML \[18] addressed the intractability of static type
> checking in dependently-typed languages by limiting type indices to a
> separate, simpler language. This technique makes it possible to check type
> equivalence without having to check equivalence of program terms, which
> themselves may include indexed types which must be checked for equivalence,
> and so on. An index erasure pass converts a well-typed Dependent ML program
> into an ML program with the same behavior. By adding singleton types for
> numbers, bounds checking for array accesses can be done by the type system
> instead of at run time \[19].

> §4 In order to eliminate shape-mismatch errors, our type system must be
> capable of tracking arrays’ shapes. Dependent typing has been used in the past
> to implement lists whose types specify their lengths via a natural number
> index. This generalizes to an array type which is indexed by a list of natural
> numbers to specify its shape. If types can contain arbitrary term expressions,
> checking whether two types are equivalent can require checking whether two
> terms are equivalent. In order to keep type checking tractable, we use the
> technique of defining a separate language of type indices, demonstrated by Xi
> et al. in Dependent ML \[18]. Separating the term and index languages
> eliminates the mutual dependence between type checking and evaluation. An
> index language should be powerful enough to express the desired type
> properties, but also simple enough that checking index equivalence is
> tractable. In Dependent ML’s case, index equivalence is checked via integer
> linear programming. The constraint domain associated with our index language
> also includes lists of natural numbers; this combination of theories is still
> decidable \[12].

Topic 1: Remora features a dependent type system for lists with rank (a list of
natural numbers), which is constrained for decidability. They take inspiration
from Dependent ML, where the rank is restricted to a separate, simpler language,
which eliminates the mutual dependence between type checking and evaluation. I
don't see this limited language for ranks described in detail. How does it
differ from the language for arrays? How does it achieve the goals of being
powerful enough for expressivity, yet being simple enough for tractability.

## First-class functions

> §1.1 Besides eliminating ambiguity and pinning down the corner cases,
> developing the formal semantics enabled us to replace some of APL and J’s ad
> hoc machinery with regular, general mechanisms. Our treatment of higher-order
> functions, for example, is much more general; this, in turn, allows us to
> extend the basic array-lifting model to permit arrays of functions (that is,
> in the function position of a function application) as well as arrays of
> arguments. This effectively generalises the language’s computational model
> from SIMD to MIMD.

How is this MIMD? That functions are now first class and can be composed with
arbitrary rank?

Topic 2: In formalizing the semantics, the authors “extend the basic
array-lifting model to permit arrays of functions (that is, in the function
position of a function application)”. Does this mean that functions are not
first class in APL and J? That seems like it would be a major shortcoming.

They say this generalizes the language's computation model from SIMD to MIMD.
How would their example of applying [sum, length]₂ to a vector, [8, 9, 6]₃, work
in APL/J without MIMD?
