# Smooth and proper variety properties

PR #4 introduces object-level smoothness and properness without defining any
new algebraic geometry.

For a variety `X : Variety k`:

```lean
X.IsSmooth := AlgebraicGeometry.Smooth X.structureMap
X.IsProper := AlgebraicGeometry.IsProper X.structureMap
```

The project also exposes full subcategories `SmoothVariety k` and
`ProperVariety k`, together with the specializations `ComplexVariety`,
`SmoothComplexVariety`, and `ProperComplexVariety`.

The base point `Spec k` over itself is included as a sanity-check example. Its
structure morphism is the identity, so mathlib proves it smooth and proper
without any additional geometric theorem.

This PR deliberately does not introduce a projective-variety predicate. Current
mathlib has `Proj` and proves properness results for projective spectra, but a
turnkey general projective-morphism API has not been identified in the pinned
4.33.0 surface. Projectivity will therefore be designed separately rather than
silently conflated with properness.

Likewise, this PR does not claim affine space is smooth in our API. That fact is
mathematically standard, but the pinned affine-space module does not export a
ready-made `Smooth` instance, so it should be proved explicitly in a later
slice if and when the required polynomial-ring smoothness bridge is clear.
