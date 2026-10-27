# Uniqueness of homogeneous cycle decompositions

`CycleDecomposition` extends note 0029's reconstruction with uniqueness.
All degrees are in `ℕ∞`, so infinite codimension remains explicit.

`Cycle.IsHomogeneous d c` means that projecting `c` to degree `d` fixes it.
Every component is homogeneous. For natural-number degrees, homogeneity is
equivalent to membership in `Variety.codimensionCycles X p`.
A homogeneous cycle has zero projection to any different degree.

`component_sum_homogeneous` computes the degree-`d` projection of a finite
sum whose term at `e` is homogeneous of degree `e`. If `d` is in the finite
index set, the projection is that term; otherwise it is zero.
`homogeneous_summand_eq_component` consequently shows that every term in
any such presentation of a cycle must be its canonical component.
`sum_homogeneous_eq_iff` compares two presentations over the same finite
index set, giving termwise equality exactly when their sums are equal.
Terms outside the index set are irrelevant and are not asserted equal.

`ext_of_components` proves equality of arbitrary cycles by equality of
all their components. `isEffective_iff_components` similarly characterizes
effectivity by the effectivity of every component.

Together with `sum_components`, these results establish existence and
uniqueness of finite homogeneous reconstruction. They do not yet package
a direct-sum equivalence, exclude infinite-codimension generators, or define
rational equivalence and Chow groups.
