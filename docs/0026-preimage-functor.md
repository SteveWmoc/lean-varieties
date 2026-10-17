# Functorial inverse images of closed subschemes

`ClosedSubschemePreimageFunctor` packages the inverse-image maps from notes
0022–0025 into categorical constructions.

For a fixed morphism `f : X ⟶ Y`,
`closedSubschemePreimageFunctor f` has domain
`(Y.toScheme.IdealSheafData)ᵒᵖ` and codomain `Variety k`. Its objects are the
inverse images, and its maps are the existing inverse-image inclusions.
Larger ideals give smaller subschemes, which accounts for the opposite
poset. The identity and composition laws are also exposed as
`closedSubschemePreimageInclusion_id` and `_comp`.

`closedSubschemePreimageRestriction f` is a natural transformation from this
functor to `closedSubschemeFunctor Y`. Its component at an ideal is the
canonical restricted map from the inverse image to the original subscheme.
Naturality says that restriction commutes with inclusion. The components
are morphisms over the same base field; the ambient varieties `X` and `Y`
need not be the same.

`closedSubschemePreimageIdNatIso X` upgrades the identity comparison from
note 0024 to a natural isomorphism. Its components are exactly
`closedSubschemePreimageIdIso X I.unop`, in both directions. Its hom is the
canonical restriction transformation, as proved by
`closedSubschemePreimageIdNatIso_hom`.

This functor varies the ideal while holding `f` fixed. It does not assert a
strict functorial construction varying the ambient variety morphism, nor
coherence laws for longer chains of base changes. No reducedness or
smoothness hypothesis is used.
