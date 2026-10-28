import LeanVarieties.CycleDecomposition
import Mathlib.Algebra.DirectSum.Basic

/-!
# The additive direct-sum decomposition of algebraic cycles

Cycles are additively equivalent to the direct sum of their homogeneous
subgroups indexed by `ℕ∞`. The canonical summation map is the inverse.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical DirectSum

universe u

namespace Variety

variable {k : Type u} [Field k] {X : Variety k}

namespace Cycle

/-- Homogeneous cycles of any degree, including infinity, form an additive subgroup. -/
def homogeneousSubgroup (X : Variety k) (d : ℕ∞) : AddSubgroup X.Cycle where
  carrier := {c | IsHomogeneous d c}
  zero_mem' := map_zero (component X d)
  add_mem' := by
    intro c e hc he
    change component X d (c + e) = c + e
    rw [map_add, hc, he]
  neg_mem' := by
    intro c hc
    change component X d (-c) = -c
    rw [map_neg, hc]

@[simp]
lemma mem_homogeneousSubgroup (d : ℕ∞) (c : X.Cycle) :
    c ∈ homogeneousSubgroup X d ↔ IsHomogeneous d c := Iff.rfl

/-- At finite degrees, the new subgroup is the existing codimension subgroup. -/
lemma homogeneousSubgroup_nat (X : Variety k) (p : ℕ) :
    homogeneousSubgroup X (p : ℕ∞) = codimensionCycles X p := by
  apply SetLike.ext
  intro c
  exact isHomogeneous_iff_mem_codimensionCycles p c

/-- Sum a finitely supported family of homogeneous cycles in the ambient group. -/
def assemble (X : Variety k) : (⨁ d : ℕ∞, homogeneousSubgroup X d) →+ X.Cycle :=
  DirectSum.coeAddMonoidHom (homogeneousSubgroup X)

@[simp]
lemma assemble_of (d : ℕ∞) (c : homogeneousSubgroup X d) :
    assemble X (DirectSum.of (fun e => homogeneousSubgroup X e) d c) = c :=
  DirectSum.coeAddMonoidHom_of (homogeneousSubgroup X) d c

/-- Projection of an assembled family recovers its coordinate. -/
lemma component_assemble (z : ⨁ e : ℕ∞, homogeneousSubgroup X e) (d : ℕ∞) :
    component X d (assemble X z) = (z d : X.Cycle) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of e c =>
    rw [assemble_of]
    have hc : IsHomogeneous e (c : X.Cycle) := c.property
    by_cases hed : e = d
    · subst e
      rw [DirectSum.of_eq_same]
      exact hc
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hed)]
      exact hc.component_eq_zero (Ne.symm hed)
  | add a b ha hb =>
    simp only [map_add, DirectSum.add_apply, AddSubgroup.coe_add, ha, hb]

/-- The summation map loses no homogeneous coordinate. -/
lemma assemble_injective (X : Variety k) : Function.Injective (assemble X) := by
  intro a b h
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  rw [← component_assemble a d, ← component_assemble b d, h]

/-- Every cycle is the sum of a finitely supported homogeneous family. -/
lemma assemble_surjective (X : Variety k) : Function.Surjective (assemble X) := by
  intro c
  refine ⟨∑ d ∈ c.degrees, DirectSum.of (fun e => homogeneousSubgroup X e) d
    ⟨component X d c, isHomogeneous_component d c⟩, ?_⟩
  simp only [map_sum, assemble_of]
  exact sum_components c

/-- The cycle group is the direct sum of its homogeneous subgroups, indexed by `ℕ∞`. -/
def directSumEquiv (X : Variety k) : X.Cycle ≃+ ⨁ d : ℕ∞, homogeneousSubgroup X d :=
  (AddEquiv.ofBijective (assemble X) ⟨assemble_injective X, assemble_surjective X⟩).symm

@[simp]
lemma directSumEquiv_symm_apply (z : ⨁ d : ℕ∞, homogeneousSubgroup X d) :
    (directSumEquiv X).symm z = assemble X z := rfl

/-- Decomposition computes exactly the canonical component in each coordinate. -/
@[simp]
lemma directSumEquiv_apply_coe (c : X.Cycle) (d : ℕ∞) :
    ((directSumEquiv X c) d : X.Cycle) = component X d c := by
  have h := component_assemble (directSumEquiv X c) d
  rw [← directSumEquiv_symm_apply, AddEquiv.symm_apply_apply] at h
  exact h.symm

/-- A homogeneous generator in the direct sum assembles to that same cycle. -/
@[simp]
lemma directSumEquiv_of (d : ℕ∞) (c : homogeneousSubgroup X d) :
    directSumEquiv X (c : X.Cycle) =
      DirectSum.of (fun e => homogeneousSubgroup X e) d c := by
  apply (directSumEquiv X).symm.injective
  rw [AddEquiv.symm_apply_apply, directSumEquiv_symm_apply, assemble_of]

end Cycle

end Variety

end

end LeanVarieties
