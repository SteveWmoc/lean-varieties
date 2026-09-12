# Smoothness of affine space

PR #5 supplies the smoothness proof deferred by PR #4.

For every field `k : Type u` and every `n : ℕ`, the affine-space module now
exports:

```lean
instance affineSpace_isSmooth (n : ℕ) :
    (affineSpace (k := k) n).IsSmooth
```

The proof applies in arbitrary universes, includes `n = 0`, and does not
assume characteristic zero or algebraic closedness.

## Proof bridge

The proof uses the pinned mathlib v4.33.0 definitions throughout:

1. `AffineSpace.SpecIso` identifies the underlying affine scheme with
   `Spec (MvPolynomial (ULift (Fin n)) k)`.
2. `AffineSpace.SpecIso_inv_over` identifies the structural morphism, after
   this isomorphism, with `Spec.map` of the coefficient map.
3. `HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap` reduce
   scheme smoothness to `Algebra.Smooth k (MvPolynomial (ULift (Fin n)) k)`.
4. Mathlib provides formal smoothness of polynomial algebras and finite
   presentation for finitely many variables. These are the two fields of
   `Algebra.Smooth`.

Smoothness is transported across the scheme isomorphism using
`MorphismProperty.cancel_left_of_respectsIso`. A local instance obtains this
isomorphism invariance from `HasRingHomProperty.eq_affineLocally` and
`RingHom.Smooth.respectsIso`; it does not depend on automatic discovery of
that instance in the pinned API. No new axiom or definition of smoothness is
introduced.

## API and scope

Importing `LeanVarieties.AffineSpace` (or the library root) exposes the
smoothness instance. The affine-space module imports `LeanVarieties.Properties`
to use the existing `Variety.IsSmooth` abbreviation.

The instance connects the standard affine-space example to the smooth-variety
property layer. Dimension, projective space, projectivity, and Hodge-theoretic
objects remain separate work.
