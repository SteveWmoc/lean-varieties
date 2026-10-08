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

Projectivity was designed separately from this smooth/proper layer. The
current [projective-variety API](0006-projective-varieties.md) defines it by a
closed immersion over the base into projective space and proves properness
as a consequence.

PR #4 deferred the proof that affine space is smooth because the pinned
mathlib affine-space module does not export a ready-made `Smooth` instance.
PR #5 supplies the polynomial-algebra bridge; see
[the affine-space smoothness note](0004-affine-space-smoothness.md).
