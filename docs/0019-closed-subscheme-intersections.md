# Scheme-theoretic intersections

For ideal sheaf data `I` and `J` on `Y : Variety k`, define

```lean
Variety.closedSubschemeIntersection Y I J :=
  Variety.closedSubscheme Y (I ⊔ J)
```

The lattice supremum is the sum of the ideals: locally, its equations are
the equations of both factors together. This is the scheme-theoretic
intersection, so it retains possible nilpotents and intersection multiplicity
information rather than taking the reduced closed subset.

## Projections and underlying closed set

`closedSubschemeIntersectionFst` and `closedSubschemeIntersectionSnd` are
canonical closed immersions to the factors. Composing either with its ambient
inclusion gives `closedSubschemeι Y (I ⊔ J)`. The range of that scheme map is
exactly the intersection of the supports of `I` and `J`.

The intersection is projective whenever the ambient variety is projective,
by the existing closed-subscheme instance. Smoothness and fixed dimension
need separate hypotheses; even smooth factors can have a singular or
nonreduced intersection.

## Universal property

For any variety `T`, suppose

```lean
f : T ⟶ Variety.closedSubscheme Y I
g : T ⟶ Variety.closedSubscheme Y J
```

have the same composite into `Y`. `closedSubschemeIntersectionLift` constructs
the map from `T` to the intersection. Its composites with the projections
are `f` and `g`, and `closedSubschemeIntersection_existsUnique` proves that
it is the unique map with those composites. This establishes the pullback
universal property in `Variety k`; it is not restricted to test objects
that are themselves closed subschemes of `Y`.

## Proof bridge

The reusable helper `closedSubschemeLift` packages mathlib's
`IsClosedImmersion.lift` as a variety morphism when the defining ideal sheaf
lies in the kernel of the ambient map. Its base-field compatibility follows
from the lift's factorization equation and the ambient variety morphism's
compatibility with `Spec k`.

A compatible pair of maps kills both ideals, using
`Scheme.Hom.le_ker_comp` and the subscheme inclusion's kernel formula.
It therefore kills their sum. The lift then follows from the helper, and
uniqueness follows because closed immersions are monomorphisms. The support
formula reuses mathlib's `IdealSheafData.support_sup`.

No transversality, reducedness, irreducibility, or characteristic assumption
is imposed, and the construction supports arbitrary field universes.
