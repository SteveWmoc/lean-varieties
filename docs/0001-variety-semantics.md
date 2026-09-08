# ADR 0001: Semantic scope of `Variety`

**Status:** Proposed

## Context

The long-term motivation for this project is to support formal statements and later formalization work involving smooth projective complex varieties, including the Hodge conjecture. The algebraic layer should nevertheless be reusable over an arbitrary base field and should build on mathlib's existing scheme theory rather than duplicate it.

The word *variety* is convention-dependent: some sources require irreducibility and reducedness, while others allow reducible varieties or use the term more broadly. That ambiguity should not be hidden inside the API.

## Proposed convention

For this project, `Variety k` will mean a separated scheme of finite type over `Spec k`, where `k` is a field.

Reducedness, irreducibility, integrality, smoothness, properness, and projectivity are to remain explicit orthogonal properties rather than fields silently built into the word `Variety`.

Thus the intended hierarchy is conceptually:

```text
Scheme
  -> scheme over Spec k
  -> Variety k          (finite type + separated)
  -> ComplexVariety     (specialize k = C)
  -> smooth/projective/etc. refinements
```

This is a project convention, not a claim that this is the unique standard mathematical definition of *variety*.

## Representation principle

`Variety k` should be a thin abstraction over mathlib's scheme-theoretic API. In particular:

- the underlying object remains a mathlib `Scheme`;
- the structure morphism to `Spec k` should reuse mathlib's over-category machinery where practical;
- finite type and separatedness should reuse mathlib's existing morphism predicates;
- morphisms of varieties should ultimately be morphisms over `Spec k`, not independent hand-written data;
- standard constructions should delegate to scheme constructions and inherit their proofs whenever possible.

No new foundational notion should be introduced merely for ergonomic convenience if mathlib already has the corresponding scheme-theoretic structure.

## Initial API goals

The first implementation phase after this ADR should provide only enough API to make the abstraction pleasant to use:

1. a representation of `Variety k`;
2. access to its underlying `Scheme` and structural morphism;
3. morphisms over the base field;
4. basic coercions/extensionality lemmas as actually needed;
5. standard examples beginning with affine space;
6. explicit predicates or instances for properties such as smoothness and properness where mathlib already supplies them.

Projective space and a projectivity API should be added only after inspecting what current mathlib already exposes around `Proj` and proper morphisms.

## Non-goals of the first implementation phase

The following are deliberately postponed:

- dimension and codimension theory;
- algebraic cycles and Chow groups;
- analytification;
- singular or sheaf cohomology wrappers;
- Hodge decomposition;
- cycle-class maps;
- any statement or proof of the Hodge conjecture.

These should be introduced only when a downstream requirement makes the needed interface clear.

## Exit criterion for the next phase

A successful first API PR should make it possible to construct and manipulate a `Variety k` without exposing unnecessary scheme plumbing, while retaining a transparent path back to the underlying mathlib objects. It should not yet attempt to solve projectivity, dimension, or Hodge-theoretic infrastructure.
