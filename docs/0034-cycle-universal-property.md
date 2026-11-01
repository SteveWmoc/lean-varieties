# The universal property of cycles

`Cycle.coefficientsEquiv X` identifies integer cycles with mathlib's finitely
supported functions `X.toScheme →₀ ℤ`. Its forward and inverse maps preserve
all coefficients, and unit generic-point cycles correspond to the standard
single-coordinate functions. The forward map uses finite support from
quasi-compactness; the inverse uses the fact that finite support is locally
finite. The underlying definition of algebraic cycles is unchanged.

For any abelian group `A` and assignment `f : X.toScheme → A`, `Cycle.lift f`
is an additive map from cycles to `A`. It is defined using mathlib's
`Finsupp.liftAddHom`. The theorem `lift_apply` gives the finite sum formula

`lift f c = ∑ x ∈ c.finite_support.toFinset, (c x) • f x`.

`lift_single` computes it on arbitrary integer multiples of a generator.
`hom_ext` shows that additive maps agreeing on unit generators agree on every
cycle. `existsUnique_lift` expresses existence and uniqueness of the extension;
`lift_generator_values` recovers an existing additive map from its generator
values. The target group may live in an independent universe.

Thus the cycle group has the free abelian group's universal property on the
set of generic points, equivalently on irreducible closed subsets. The API
continues to use mathlib's cycle representation, rather than introducing a
second free-group model. This is useful for defining later maps by generators,
but it does not itself construct a geometric pushforward, rational equivalence,
a Chow group, or a cohomological cycle class.
