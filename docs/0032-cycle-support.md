# Geometric support of cycles

`Cycle.geometricSupport c` is the closure of the set of points with nonzero
coefficients, packaged as a closed subset. It includes specializations of the
generic points: coefficient support alone is generally not closed.

`geometricSupport_eq_iUnion` identifies it with the finite union of the
irreducible closed subsets indexed by nonzero coefficients. Finiteness follows
from quasi-compactness, as in note 0027.

`geometricSupport_le_iff` relates containment in a closed subset to the existing
`supportedOn` subgroup. Empty geometric support is equivalent to a zero cycle.
For arbitrary sums, support is contained in the union; cancellation may make
this containment strict. For effective cycles, `IsEffective.support_add` and
`IsEffective.geometricSupport_add` prove equality, first at the coefficient
level and then for the closed geometric support.

This is a statement about closed subsets, not a choice of scheme structure on
support. It does not define intersections of cycles or rational equivalence.
