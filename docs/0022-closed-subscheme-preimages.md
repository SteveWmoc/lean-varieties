# Inverse images of closed subschemes

For `f : X ⟶ Y` and ideal-sheaf data `I` on `Y.toScheme`,
`Variety.closedSubschemePreimage f I` is the closed subscheme of `X` defined
by mathlib's `I.comap f.hom.left`. This retains the scheme structure,
including nilpotents; it does not replace the ideal with its radical.

The source is a variety because it is a closed subscheme of `X`.
`closedSubschemePreimageι f I` is its canonical closed immersion into `X`.
`closedSubschemePreimageMap f I` is the restriction into `closedSubscheme Y I`.
Both maps are over the original base field. The theorem
`closedSubschemePreimageMap_ι` says that the two composites to `Y` agree.
Its reassociated form is also available to the simplifier.

`closedSubschemePreimage_range` identifies the range of the inclusion with
the set-theoretic inverse image of `I.support` under the underlying scheme
map. This describes the point set, while the construction retains the full
pulled-back ideal. If `X` is projective, the inverse image is projective.
Smoothness is not automatic and no smoothness instance is supplied.

Mathlib constructs the ideal using a scheme pullback and supplies a comparison
isomorphism. This module packages the object and maps in `Variety k`; the
pullback universal property in that category is proved in
[note 0023](0023-preimage-pullbacks.md).
