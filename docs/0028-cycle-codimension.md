# Fixed-codimension cycle subgroups

`CycleCodimension` starts geometric grading of the cycle group from note 0027.

## Codimension convention

`Cycle.generatorClosed x` packages the irreducible closed closure of the
scheme point `x`. `Cycle.generatorCodimension x` is its `Order.coheight`
in the inclusion poset `TopologicalSpace.IrreducibleCloseds X.toScheme`.
It therefore measures lengths of chains of irreducible closed supersets,
which is the topological codimension convention. Values lie in `ℕ∞`;
infinite coheight is retained, never converted to zero with `toNat`.

This definition works for singular generators and reducible or nonreduced
ambient varieties. It does not use smooth relative dimension or subtract
natural-number dimensions. No equality with local-ring dimension or other
codimension definitions is claimed here.

## Subgroups and coefficients

`Cycle.supportedOn X S` is the additive subgroup of cycles whose nonzero
coefficients lie in the set of generic points `S`. Membership is equivalent
to support containment, and a single generator belongs whenever its index
lies in `S`. For a coefficient-one generator, this is an equivalence.

`Variety.codimensionCycles X p` specializes this construction to points of
codimension `p`, for a natural number `p`. Addition, negation, subtraction,
and integer scalar multiplication are inherited from `AddSubgroup`.
`mem_codimensionCycles` gives the coefficient-vanishing criterion, and
`single_one_mem_codimensionCycles_iff` identifies exactly which coefficient-one
generators have degree `p`. A cycle belonging to two distinct finite degrees
is zero, by `eq_zero_of_mem_codimensionCycles_of_ne`.

[Note 0029](0029-cycle-components.md) adds component projections and finite
reconstruction indexed by `ℕ∞`. The API does not yet establish finiteness
of every generator's codimension,
a direct-sum decomposition of all cycles, dimension formulas for affine or
projective spaces, rational equivalence, or cycle classes in cohomology.
