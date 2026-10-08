# Affine space example

PR #3 adds affine `n`-space over a field as the first standard object in the
`Variety k` API.

For `k : Type u` and `n : ℕ`, the underlying scheme is mathlib's affine space

```lean
AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) (baseScheme k)
```

The universe lift is required because mathlib indexes affine-space coordinates
by a type in the same universe as the base scheme.

The structural morphism is already an affine morphism in mathlib. For finite
coordinate index type it is also locally of finite presentation, hence locally
of finite type. Affineness supplies quasi-compactness and separatedness, so the
scheme satisfies the project's definition of `Variety k` without any new
algebraic-geometry proofs.

The original construction did not add smoothness or dimension witnesses.
These are now supplied by [0004](0004-affine-space-smoothness.md) and
[0013](0013-standard-space-dimension.md). Projective space is constructed in
[0005](0005-projective-space.md); a products API remains future work.
