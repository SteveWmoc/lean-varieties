# Projective varieties

PR #7 defines projectivity using the projective spaces constructed in
[PR #6](0005-projective-space.md).

## Definition

For `X : Variety k`, the proposition `X.IsProjective` asserts

```lean
∃ (n : ℕ) (i : X.toScheme ⟶ Variety.projectiveScheme k n),
  AlgebraicGeometry.IsClosedImmersion i ∧
    i ≫ Variety.projectiveStructureMap k n = X.structureMap
```

The final equation requires the embedding to be over `Spec k`. A closed
immersion of underlying schemes alone would not record compatibility with
the specified field structure.

`Variety.IsProjective` is a proposition-valued class whose single field
proves this existential statement. It does not choose an embedding or make
the embedding part of the variety's data. The generated
`Variety.isProjective_iff` exposes the defining equivalence.

The base definition of `Variety k` continues to require finite type and
separatedness. Smoothness, reducedness, and irreducibility are independent
conditions. The projectivity definition applies to every field and every
field universe.

## Closure and properness

`Variety.IsProjective.of_closedImmersion` proves that a closed immersion
over the base into a projective variety makes its source projective. The
proof composes the given closed immersion with a projective-space embedding
of the target and checks the equation to the base.

`Variety.IsProjective.isProper` exposes properness as a typeclass instance.
A closed immersion is finite and hence proper in pinned mathlib v4.33.0;
its composite with the proper structural morphism of projective space is
proper. The equation to the base identifies that composite with
`X.structureMap`.

Properness is a consequence of the embedding definition. No converse is
asserted.

`Variety.projectiveSpace_isProjective` supplies the standard examples using
identity closed immersions, including `n = 0`.

## Categories for downstream use

The file exports full subcategories

- `ProjectiveVariety k`;
- `SmoothProjectiveVariety k`;

and their complex specializations

- `ProjectiveComplexVariety`;
- `SmoothProjectiveComplexVariety`.

Morphisms are inherited from `Variety k` and therefore commute with the maps
to the base. Instances expose the defining properties of each category's
underlying variety; properness follows from the projectivity instance.

`SmoothProjectiveComplexVariety` now provides an object type for the
algebraic input to a later Hodge statement. This slice supplies neither
cohomology nor algebraic cycles nor a statement of the conjecture.

## Next boundary

The standard affine charts and smoothness of projective space remain to be
proved. Defining the smooth projective category does not assert that the
projective-space examples already carry a smoothness proof.
