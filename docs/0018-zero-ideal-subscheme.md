# The zero ideal defines the ambient variety

For `Y : Variety k`, the zero ideal sheaf imposes no equations. Its closed
subscheme is canonically isomorphic to `Y` over `Spec k`:

```lean
Variety.closedSubschemeBotIso Y : Variety.closedSubscheme Y ⊥ ≅ Y
```

The forward map is exactly `Variety.closedSubschemeι Y ⊥`. The underlying
scheme map of the inverse is the inverse of mathlib's zero-ideal subscheme
inclusion. A structural-map compatibility lemma records that this inverse
also preserves the specified base field.

## Detecting the whole ambient subscheme

`Variety.isIso_closedSubschemeι_iff_eq_bot` proves that the canonical
inclusion of the subscheme defined by `I` is an isomorphism if and only if
`I = ⊥`. This lifts mathlib's existing
`Scheme.isIso_subschemeι_iff_eq_bot`: both the full-subcategory inclusion and
the forgetful functor from the over-category reflect isomorphisms.

The criterion concerns the **canonical inclusion**. An abstract isomorphism
between a subscheme and its ambient variety need not identify that inclusion
with an isomorphism. No reducedness or irreducibility assumption is used.

## Compatibility with inclusions and geometric properties

For every ideal sheaf `I`, `Variety.closedSubschemeInclusion_bot` identifies
the inclusion associated to `⊥ ≤ I` with

```lean
Variety.closedSubschemeι Y I ≫ (Variety.closedSubschemeBotIso Y).inv
```

Thus the ideal-sheaf functor's zero-ideal object agrees with the ambient
variety through the specified isomorphism, including its incoming maps.

Instances transport ambient smoothness, properness, and smooth relative
dimension through this isomorphism. Ambient projectivity is already inherited
by every closed subscheme through the existing closed-immersion instance.
These additional smoothness and dimension instances apply only to the zero
ideal; they do not assert that arbitrary closed subschemes are smooth.
