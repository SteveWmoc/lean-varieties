# First algebraic-cycle API

`AlgebraicCycle` reuses mathlib's algebraic cycles on the underlying scheme
of a variety. `Variety.Cycle X` is the integer-coefficient group.

## Geometric meaning

Mathlib represents cycles by functions on scheme points with locally finite
support. A scheme point is the unique generic point of its irreducible closed
closure, so a coefficient at that point represents the corresponding
irreducible closed subset, not merely a closed point. The lemma
`Cycle.generatorCarrier_isIrreducible` records irreducibility of that closure;
mathlib's `IsIrreducible` includes nonemptiness.

This is the standard indexing for cycles by integral closed subvarieties,
whose reduced scheme structures can be recovered from their closed subsets.
This module does not yet construct those reduced subscheme objects or prove
a new generic-point equivalence.

## Finite sums and coefficients

`Cycle.ext` proves equality coefficient by coefficient.
`Cycle.finite_support` shows that each cycle has finite support: the
structural map is quasi-compact and the base spectrum is compact, so local
finiteness becomes global finiteness. No Hausdorff assumption is used.

`Cycle.single x n` gives coefficient `n` at `x` and zero elsewhere.
`Cycle.sum_single` reconstructs every cycle as the finite sum over its
nonzero coefficients. Addition, subtraction, negation, and integer scalar
multiplication are inherited directly from mathlib.
`Cycle.IsEffective` means coefficientwise nonnegativity; zero, addition,
and nonnegative single generators preserve effectivity.

## Scope toward Hodge theory

These cycles are **ungraded**: neither dimension nor codimension is imposed.
The current smooth-relative-dimension API is not used to assign dimensions
to possibly singular cycle generators. Codimension grading, multiplicities
of general closed subschemes, rational equivalence, Chow groups, geometric
pushforward/pullback wrappers, and cycle classes in cohomology remain future
work. In particular, scheme-theoretic inverse images from earlier modules
are not asserted to define pullback of cycles along arbitrary morphisms.
