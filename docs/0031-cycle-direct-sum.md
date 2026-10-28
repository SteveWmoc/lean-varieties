# The additive direct-sum decomposition

`CycleDirectSum` packages the preceding reconstruction and uniqueness results
as an equivalence with mathlib's dependent `DirectSum`.

`Cycle.homogeneousSubgroup X d` consists of cycles fixed by the degree-`d`
projection. It is an additive subgroup for every `d : ℕ∞`. At a finite degree
`p`, `homogeneousSubgroup_nat` identifies it with `codimensionCycles X p`.

`Cycle.assemble X` is the canonical additive map from the direct sum of these
subgroups to the ambient cycle group, using `DirectSum.coeAddMonoidHom`.
`component_assemble` proves that projecting the assembled cycle recovers the
corresponding coordinate. This gives injectivity. Finite reconstruction
from note 0029 gives surjectivity.

`Cycle.directSumEquiv X` is the resulting additive equivalence, oriented from
cycles to the direct sum. Its inverse is `assemble`. The theorem
`directSumEquiv_apply_coe` identifies every decomposed coordinate with the
canonical component. `directSumEquiv_of` identifies a homogeneous cycle with
its single-coordinate direct-sum inclusion. Addition, negation, subtraction,
and integer multiples are respected by the additive equivalence.

The grading includes infinity. No claim that all generator codimensions are
finite is used, and the result does not replace `ℕ∞` with `ℕ`. Dimension
comparisons, rational equivalence, Chow groups, and cohomological cycle classes
remain separate future work.
