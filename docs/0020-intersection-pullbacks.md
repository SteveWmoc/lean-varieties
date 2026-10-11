# Intersections through mathlib's pullback API

The [intersection construction](0019-closed-subscheme-intersections.md)
already supplies existence and uniqueness of lifts. This module exposes that
result in the standard categorical API:

```lean
Variety.closedSubschemeIntersection_isPullback Y I J :
  IsPullback (Variety.closedSubschemeIntersectionFst Y I J)
    (Variety.closedSubschemeIntersectionSnd Y I J)
    (Variety.closedSubschemeι Y I) (Variety.closedSubschemeι Y J)
```

The witness provides the usual `IsPullback.lift`, `hom_ext`, and square-pasting
tools. The corresponding `HasPullback` instance lets downstream code use
`Limits.pullback`, its projections, and `Limits.pullback.lift` directly for
these two canonical inclusions.

## Comparing explicit and chosen objects

`closedSubschemeIntersectionPullbackIso Y I J` identifies the ideal-sum
intersection with the pullback selected by mathlib's limit machinery. The
objects need not be definitionally equal. Projection compatibility lemmas
for the isomorphism and its inverse preserve both maps into the factors.

The standard lift obtained from the square witness equals the explicit
`closedSubschemeIntersectionLift`. Composing that explicit lift with the
comparison isomorphism's forward map gives `Limits.pullback.lift`. These
equations have simp and reassociation support for use inside larger diagrams.

## Scope

All results are in `Variety k`, whose morphisms preserve `Spec k`. The
`HasPullback` instance is specific to canonical closed-subscheme inclusions;
it does not assert that every pair of variety morphisms has a pullback or
that the forgetful functor preserves arbitrary limits. No new geometric
proof, smoothness hypothesis, or choice of a reduced intersection is added.
