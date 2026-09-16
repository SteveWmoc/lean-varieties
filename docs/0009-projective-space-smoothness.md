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

Smoothness in mathlib is Zariski-local on the source. Applying
`IsZariskiLocalAtSource.iff_of_iSup_eq_top` reduces smoothness of the
projective structural morphism to smoothness after restriction to every
coordinate open. The compatibility theorem rewrites each restricted morphism
as the affine-space structural morphism preceded by a scheme isomorphism.
Both factors are smooth, so the local goals are discharged by the existing
smoothness instances.

## API

The new exported instance is

```lean
Variety.projectiveSpace_isSmooth (n : ℕ) :
  (Variety.projectiveSpace (k := k) n).IsSmooth
```

It applies to every field and every natural number `n`, including `n = 0`.
No characteristic assumption or algebraic-closedness assumption is used.

Together with the existing projectivity instance, projective space now gives a
canonical object of `SmoothProjectiveVariety k` at the property level. This
slice does not yet add a dedicated constructor for that full-subcategory
object, dimension theory, transition-function formulas, cycles, cohomology,
or any Hodge-theoretic definitions.

The Lean and mathlib versions remain pinned to v4.33.0.
