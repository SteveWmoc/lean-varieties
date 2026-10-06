# Constructing varieties from closed subschemes

The earlier closed-immersion API required the source to be supplied as a
`Variety k`. The new construction starts with a scheme and a closed immersion
into an existing variety:

```lean
Variety.ofClosedImmersion Y i
Variety.closedImmersionι Y i
```

Here `Y : Variety k` and `i : X ⟶ Y.toScheme` is a closed immersion. Its source
is separated and of finite type over `Spec k`: these properties follow by
composing the closed immersion with `Y.structureMap`. The inclusion is then
packaged as a morphism in `Variety k`, carrying compatibility with the base.

For ideal sheaf data `I : Y.toScheme.IdealSheafData`, the specialized API is:

```lean
Variety.closedSubscheme Y I
Variety.closedSubschemeι Y I
```

It uses mathlib's `I.subscheme` and `I.subschemeι`. Simp lemmas expose the
underlying scheme, the composite structural map, and the underlying inclusion.
The inclusion's closed-immersion property is available as an instance.

If the ambient variety is projective, both source constructions inherit
projectivity automatically through the existing closed-immersion theorem.
They can therefore be passed to the previously introduced smooth projective
packaging constructors after establishing source smoothness and, when needed,
its fixed relative dimension.

The construction follows the project's convention that varieties are separated
schemes of finite type. It permits nonreduced or singular closed subschemes;
smoothness, reducedness, and integrality are separate properties.
