# Intersection symmetry and absorption

`ClosedSubschemeIntersectionLaws` supplies canonical isomorphisms over the base
field for the intersection objects introduced in notes 0019 and 0020.

## Symmetry

`closedSubschemeIntersectionSwap Y I J` maps the intersection of `I` and `J`
to the intersection of `J` and `I`. It is constructed using the unique lift
of the two projections in reverse order. The `_fst` and `_snd` lemmas show
that it swaps the projections, and `_swap` proves that swapping twice is the
identity. `closedSubschemeIntersectionSymmetry` packages these maps as an
isomorphism.

## Absorption

If `h : J ≤ I`, then the subscheme defined by `I` is contained in the subscheme
defined by `J`. `closedSubschemeIntersectionAbsorption Y I J h` identifies
the intersection with the first subscheme. Its forward map is the first
projection, and its inverse is the ideal-inclusion map induced by
`I ⊔ J ≤ I`. The inverse followed by the first projection is the identity;
followed by the second projection it is `closedSubschemeInclusion Y h`.

`closedSubschemeIntersectionSelfIso Y I` specializes absorption to `I = J`.
This concerns the scheme-theoretic fiber product of a closed immersion with
itself, not a transverse or derived intersection. No reducedness or smoothness
hypothesis is used, and nilpotents are retained.
