# Inverse images as categorical pullbacks

`ClosedSubschemePreimagePullback` proves that the inverse-image square from
note 0022 is a pullback in `Variety k`.

For `f : X ⟶ Y`, ideal-sheaf data `I` on `Y`, and maps `a : T ⟶ X` and
`b : T ⟶ closedSubscheme Y I` satisfying
`a ≫ f = b ≫ closedSubschemeι Y I`, use
`closedSubschemePreimageLift f I a b w`. Its composites with the inclusion
and restricted map are `a` and `b`, by the `_ι` and `_map` lemmas.
`closedSubschemePreimage_existsUnique` records both equations and uniqueness.
The stronger `closedSubschemePreimage_hom_ext` needs only equality after
composition with the inclusion into `X`.

The lift is constructed using the scheme pullback and mathlib's `comapIso`.
Its structure-map equation is checked explicitly, making it a morphism over
the same base field. This works without smoothness or reducedness assumptions.

`closedSubschemePreimage_isPullback f I` gives an `IsPullback` witness.
The targeted `HasPullback f (closedSubschemeι Y I)` instance allows use of
mathlib's chosen pullback. `closedSubschemePreimagePullbackIso` compares it
to the explicit inverse image; forward and inverse projection equations and
`closedSubschemePreimageLift_pullbackIso_hom` identify their maps and lifts.
This does not assert the existence of arbitrary pullbacks in the variety
category or a general limit-preservation theorem for the forgetful functor.
