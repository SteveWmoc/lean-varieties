# Inclusions between closed subschemes

For ideal sheaf data `I ≤ J` on `Y : Variety k`, the new map

```lean
Variety.closedSubschemeInclusion Y h
```

goes from `Variety.closedSubscheme Y J` to `Variety.closedSubscheme Y I`.
The direction reverses the ideal inclusion: imposing more equations makes
the closed subscheme smaller.

This map uses mathlib's `Scheme.IdealSheafData.inclusion h`, with the
compatibility proof needed to regard it as a variety morphism over `k`.
Its underlying scheme map is a closed immersion, available as an instance.

The API records three laws, reusing the corresponding mathlib results:

- Composing with the inclusion into `Y` gives the original inclusion of
  the source subscheme (`closedSubschemeInclusion_ι`).
- The reflexive ideal inclusion gives the identity map
  (`closedSubschemeInclusion_id`).
- Two successive ideal inclusions give the composite closed-subscheme
  inclusion (`closedSubschemeInclusion_comp`).

The inclusion and composition laws have reassociated simp versions.
These constructions assemble into `Variety.closedSubschemeFunctor Y`, a
functor from the opposite of the ideal-sheaf poset to `Variety k`.

This is a reusable interface for nested closed subschemes and later diagrams
of algebraic subvarieties. It retains scheme structure, including possible
nilpotents, rather than reducing a subscheme to its underlying point set.
