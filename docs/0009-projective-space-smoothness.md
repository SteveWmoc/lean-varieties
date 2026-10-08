# Smoothness of projective space

PR #10 proves that projective `n`-space over an arbitrary field is smooth.
The proof deliberately reuses the standard affine charts constructed in PRs
#8 and #9 rather than introducing a second polynomial-ring argument.

## Local proof

For every homogeneous coordinate `Xᵢ`, the standard open `D₊(Xᵢ)` is
isomorphic over `Spec k` to affine `n`-space. PR #9 exports this as
`ProjectiveSpace.coordinateOpenIsoAffineSpace`, together with the structural
map compatibility theorem

```lean
ProjectiveSpace.coordinateOpenIsoAffineSpace_hom_structureMap
```

The coordinate opens cover all of projective space by
`ProjectiveSpace.iSup_coordinateOpen_eq_top`.

Smoothness in mathlib is Zariski-local on the source. The implementation uses
`HasRingHomProperty.iff_of_source_openCover` to reduce smoothness of the
projective structural morphism to smoothness after restriction to every
coordinate open. The compatibility theorem rewrites each restricted morphism
as the affine-space structural morphism preceded by a scheme isomorphism.
Isomorphism invariance reduces each local goal to the existing affine-space
smoothness witness, which is converted to the ring-level condition by
`HasRingHomProperty.appTop`.

## API

The new exported instance is

```lean
Variety.projectiveSpace_isSmooth (n : ℕ) :
  (Variety.projectiveSpace (k := k) n).IsSmooth
```

It applies to every field and every natural number `n`, including `n = 0`.
No characteristic assumption or algebraic-closedness assumption is used.

Together with the existing projectivity instance, projective space now gives a
canonical object of `SmoothProjectiveVariety k` at the property level.
Dedicated constructors are now supplied by
[0010](0010-projective-space-objects.md), and fixed dimension by
[0013](0013-standard-space-dimension.md). Transition-function formulas,
cycles, cohomology, and Hodge-theoretic definitions remain future work.

The Lean and mathlib versions are pinned to v4.34.1.
