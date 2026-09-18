# Closed subvarieties of projective varieties

PR #12 makes projectivity inheritance ergonomic for morphisms in the
`Variety k` category.

The existing theorem

```lean
Variety.IsProjective.of_closedImmersion
```

works with a raw morphism of schemes and therefore asks explicitly for the
equation saying that the closed immersion commutes with the two structural
morphisms to `Spec k`.

For a morphism

```lean
f : X ⟶ Y
```

in `Variety k`, that equation is already part of the morphism data: varieties
form a full subcategory of the over-category of `Spec k`. PR #12 exposes this
as

```lean
Variety.IsProjective.of_closedImmersion_hom
```

for any variety morphism whose underlying scheme morphism is a closed
immersion and whose target is projective.

Two thin packaging constructors are also added:

```lean
ProjectiveVariety.ofClosedImmersion
SmoothProjectiveVariety.ofClosedImmersion
```

The second requires the source variety to be smooth separately. In particular,
this PR does **not** assert that an arbitrary closed subvariety of a smooth or
projective variety is smooth.

This API is intended to support later projective hypersurface and cycle
constructions: once a closed subvariety is represented by a morphism in
`Variety k`, its compatibility with the base field no longer has to be
reproved by hand.
