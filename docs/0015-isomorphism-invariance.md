# Geometric properties are invariant under variety isomorphisms

For `e : X ≅ Y` in `Variety k`, `Variety.schemeIso e` is the underlying
scheme isomorphism. Its forward map commutes with the structural maps to
`Spec k`, as recorded by `Variety.schemeIso_hom_structureMap` and its
automatically generated reassociated lemma.

The new transport lemmas take a property instance on `Y` and prove it on `X`:

- `Variety.isSmooth_of_iso e`
- `Variety.isProper_of_iso e`
- `Variety.isProjective_of_iso e`
- `Variety.isSmoothOfDimension_of_iso e n`

Each has a corresponding `_iff_of_iso` lemma equating the properties on
`X` and `Y`. Applying the transport lemma to `e.symm` reverses the direction.
These are explicit lemmas rather than global instances, so instance search
does not have to search for isomorphisms.

Smoothness and properness use composition with the underlying scheme
isomorphism. Projectivity follows from the existing closed-immersion
inheritance theorem, since an isomorphism is a closed immersion. For fixed
smooth dimension, the isomorphism has relative dimension zero, so composing
it with a smooth morphism of relative dimension `n` preserves `n`.

This API lets later constructions prove geometric properties in a convenient
presentation and transport them to an isomorphic variety over the same field.
The compatibility with the base field matters: the hypothesis is an
isomorphism of varieties, not merely of their underlying schemes.
