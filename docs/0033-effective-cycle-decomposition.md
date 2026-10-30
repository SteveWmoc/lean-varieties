# Canonical effective decomposition

Integer cycles already inherit mathlib's pointwise lattice-ordered additive
group structure from `Function.locallyFinsupp`. This module uses the existing
notation `c⁺` and `c⁻`, with coefficients `max (c x) 0` and `max (-c x) 0`.
Both parts are effective. The inherited theorem `posPart_sub_negPart` states
`c⁺ - c⁻ = c`; no parallel definition of these operations is introduced.

`exists_effective_sub` packages existence of an effective difference
presentation with disjoint coefficient supports. `effective_sub_parts` and
`effective_decomposition_unique` prove that disjointness makes the presentation
unique. Without it, one could add the same effective cycle to both terms.

`support_eq_union_parts` and `disjoint_support_parts` partition the nonzero
generic-point coefficients. `geometricSupport_eq_sup_parts` then identifies
the closed support with the union of the closed supports of the parts.
**These closed supports need not be disjoint:** distinct irreducible closed
subsets can intersect. Disjointness here concerns the generators carrying
coefficients, not all their specializations.

Both sign operations commute with every codimension projection, including
infinite codimension. `parts_mem_codimensionCycles` shows that a cycle of
fixed finite codimension has both effective parts in that same subgroup.
This supplies effective representatives for the additive cycle groups;
it does not impose rational equivalence or construct a Chow group.
