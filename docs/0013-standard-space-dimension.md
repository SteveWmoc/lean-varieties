# Standard spaces of fixed dimension

`Variety.affineSpace_isSmoothOfDimension` and
`Variety.projectiveSpace_isSmoothOfDimension` witness relative dimension `n`
for affine and projective `n`-space over any field.

The affine proof uses the pinned mathlib v4.34.1 instance for `ULift (Fin n)`.
The projective proof checks relative dimension on the standard coordinate
open cover, transporting the affine witness across the existing chart
isomorphisms over the base.

Canonical objects are available as `SmoothVarietyOfDimension.affineSpace`,
`SmoothVarietyOfDimension.projectiveSpace`, and
`SmoothProjectiveVarietyOfDimension.projectiveSpace`. Each has a simp lemma
exposing its underlying variety. The constructions also apply when `n = 0`.
