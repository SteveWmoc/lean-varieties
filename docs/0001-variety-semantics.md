# ADR 0001: Semantic scope of `Variety`

**Status:** Accepted

## Context

The long-term motivation for this project is to support formal statements and later formalization work involving smooth projective complex varieties, including the Hodge conjecture. The algebraic layer should nevertheless be reusable over an arbitrary base field and should build on mathlib's existing scheme theory rather than duplicate it.

The word *variety* is convention-dependent: some sources require irreducibility and reducedness, while others allow reducible varieties or use the term more broadly. That ambiguity should not be hidden inside the API.

## Convention

For this project, `Variety k` means a separated scheme of finite type over `Spec k`, where `k` is a field.

Reducedness, irreducibility, integrality, smoothness, properness, and projectivity remain explicit orthogonal properties rather than fields silently built into the word `Variety`.

The hierarchy starts with a scheme over `Spec k`, restricts to finite type
and separatedness to obtain `Variety k`, and then adds geometric properties
through full subcategories. `ComplexVariety` specializes the field to `ℂ`.

This is a project convention, not a claim that this is the unique standard mathematical definition of *variety*.

## Representation decision

`Variety k` is implemented as a full subcategory of mathlib's `Over (Spec k)`.
The object property requires the structural morphism to be:

- `LocallyOfFiniteType`;
- `QuasiCompact`;
- `IsSeparated`.

The first two conditions together are the scheme-theoretic finite-type condition used by mathlib. This representation has several consequences by construction:

- the underlying object remains a mathlib `Scheme`;
- the structure morphism is the morphism already stored by the over-category object;
- morphisms of varieties are automatically morphisms over `Spec k`;
- identities and composition are inherited from the full-subcategory/category machinery;
- the defining morphism properties can be exposed as instances without duplicating their definitions.

No new foundational notion is introduced merely for ergonomic convenience when mathlib already supplies the corresponding scheme-theoretic structure.

## Initial API goals

The first implementation phase provides only enough API to make the abstraction pleasant to use:

1. a representation of `Variety k`;
2. access to its underlying `Scheme` and structural morphism;
3. morphisms over the base field;
4. constructors from over-category objects and structural morphisms;
5. inherited instances for the defining properties.

The core representation was validated before adding standard examples.
[Affine space](0002-affine-space.md), [projective space](0005-projective-space.md),
and the [projectivity API](0006-projective-varieties.md) are now implemented
using mathlib's affine-space, `Proj`, and morphism-property infrastructure.

## Non-goals of the first implementation phase

The first phase postponed the following:

- dimension and codimension theory;
- algebraic cycles and Chow groups;
- analytification;
- singular or sheaf cohomology wrappers;
- Hodge decomposition;
- cycle-class maps;
- any statement or proof of the Hodge conjecture.

These should be introduced only when a downstream requirement makes the needed interface clear.

Fixed smooth relative dimension is now available; see
[0012](0012-smooth-dimension.md) and [0013](0013-standard-space-dimension.md).
General dimension and codimension theory and the Hodge-theoretic items above
remain outside the implemented API.

## Exit criterion

The core API should make it possible to construct and manipulate a `Variety k` without exposing unnecessary scheme plumbing, while retaining a transparent path back to the underlying mathlib objects. It should not yet attempt to solve projectivity, dimension, or Hodge-theoretic infrastructure.
