# Inverse images preserve scheme-theoretic intersections

`ClosedSubschemePreimageIntersection` identifies the inverse image of the
intersection defined by `I ⊔ J` with the intersection of the inverse images.
The construction retains the full ideal-sheaf data, including nilpotents.
No smoothness or reducedness hypothesis is used.

## Inclusions between inverse images

If `h : I ≤ J`, `closedSubschemePreimageInclusion f h` is the canonical map
from the inverse image of `J` to that of `I`. It is induced by monotonicity
of ideal pullback. Its `_ι` lemma identifies the composite into the ambient
source; `_map` says that restriction back to the original closed subschemes
commutes with the ideal-inclusion maps.

## Intersection comparison

`closedSubschemePreimageIntersectionIso f I J` goes from the inverse image
of `I ⊔ J` to the intersection defined by
`I.comap f.hom.left ⊔ J.comap f.hom.left`. It uses mathlib's `comap_sup`
and the equality-transport comparison from note 0024.

Forward and inverse inclusion equations show that the comparison is over
the ambient source. The `_hom_fst`, `_hom_snd`, `_inv_fst`, and `_inv_snd`
lemmas identify the two projections with the inverse-image inclusions
induced by `le_sup_left` and `le_sup_right`. Finally, `_hom_fst_map` and
`_hom_snd_map` identify the maps all the way back to the original factors.
These equations have reassociated simplification lemmas.

This concerns ordinary scheme-theoretic intersections. It makes no claim
about derived intersections or preservation of arbitrary limits.
