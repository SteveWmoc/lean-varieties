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

This PR deliberately does not add dimension theory, smoothness, products, or
projective space. Those should build on the core example in later PRs.
