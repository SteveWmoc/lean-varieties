# Smooth varieties of fixed dimension

PR #13 introduces the dimension-aware smooth variety layer needed by later
Hodge-theoretic statements.

For a variety `X` over a field `k`, the project uses mathlib's existing
scheme-theoretic predicate

```lean
SmoothOfRelativeDimension n X.structureMap
```

as the meaning of “`X` is smooth of dimension `n` over `k`.” This is
exposed as

```lean
Variety.IsSmoothOfDimension X n
```

and comes with the implication

```lean
Variety.IsSmoothOfDimension.isSmooth
```

to the previously defined `Variety.IsSmooth`.

The PR packages two fixed-dimension full subcategories:

```lean
SmoothVarietyOfDimension k n
SmoothProjectiveVarietyOfDimension k n
```

with instances exposing their smoothness, fixed relative dimension, and (for
the second category) projectivity. Canonical forgetful functors

```lean
SmoothVarietyOfDimension.forgetDimension
SmoothProjectiveVarietyOfDimension.forgetDimension
```

drop only the dimension witness and land in the existing smooth and smooth
projective categories.

For the eventual Hodge statement, the complex specializations are also named:

```lean
SmoothComplexVarietyOfDimension n
SmoothProjectiveComplexVarietyOfDimension n
```

The standard-space witnesses are now implemented separately in
[0013](0013-standard-space-dimension.md), using the affine-space instance
available in the pinned mathlib v4.34.1 and the existing projective charts.
