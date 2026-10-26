# Codimension components and finite reconstruction

`Cycle.component X d : X.Cycle →+ X.Cycle`, for `d : ℕ∞`, keeps the
coefficient at a generic point precisely when its generator has codimension
`d`; it sets all other coefficients to zero. Its support is contained in the
original cycle's finite support, so the result is again a cycle.

The additive homomorphism structure supplies compatibility with zero,
addition, negation, subtraction, and integer multiples. `component_apply`
is the coefficient formula. `component_idem` says that projecting twice
onto one degree is the same as projecting once;
`component_component_of_ne` says that projections onto distinct degrees
annihilate one another. Components of effective cycles remain effective.

For a natural number `p`, `component_mem_codimensionCycles` puts the degree-`p`
component in note 0028's subgroup. `component_eq_self_of_mem` shows that this
projection fixes every cycle already in that subgroup.

`Cycle.degrees c` is the finite image of the nonzero coefficient indices
under `generatorCodimension`. `sum_components` reconstructs `c` as the sum
of its components over this finite set. This theorem includes degree
infinity if it occurs: it does not assume that every generator has finite
codimension, and it does not discard the infinite-codimension coefficients.

This is finite reconstruction inside the ambient cycle group. A bundled
direct-sum equivalence, finiteness of all geometric codimensions, rational
equivalence, and Chow groups remain future work.
