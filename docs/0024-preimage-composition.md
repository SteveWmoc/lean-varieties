# Identity and composition of inverse images

`ClosedSubschemePreimageComposition` gives canonical isomorphisms of varieties
for inverse images along identity maps and composites.

`closedSubschemeCongr X h` first packages an equality of ideal-sheaf data as
an isomorphism of closed subschemes over `X`. Both its forward and inverse
maps commute with the canonical inclusions. It uses equality transport,
so it introduces no choices beyond those already in the closed-subscheme
construction.

`closedSubschemePreimageIdIso X I` identifies the inverse image along
`𝟙 X` with the original closed subscheme. Its forward map is exactly
`closedSubschemePreimageMap (𝟙 X) I`. Forward and inverse inclusion equations
are available to the simplifier, including reassociated versions.

For `f : X ⟶ Y`, `g : Y ⟶ Z`, and ideal-sheaf data `I` on `Z`,
`closedSubschemePreimageCompIso f g I` goes from the inverse image along
`f ≫ g` to the successive inverse image along `g` and then `f`.
It comes from mathlib's equality
`I.comap (f.hom.left ≫ g.hom.left) = (I.comap g.hom.left).comap f.hom.left`.
Both directions preserve the inclusion into `X`; they also identify the map
to the original closed subscheme with the composite of the two restricted
maps. These equations allow changing presentations without losing the maps.

No reducedness or smoothness hypothesis is used. Compatibility with
intersections and coherence for longer chains are not asserted in this module.
