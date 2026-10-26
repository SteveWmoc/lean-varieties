import LeanVarieties.CycleCodimension

/-!
# Codimension components of algebraic cycles

Coefficientwise projections split a cycle into finitely many codimension
components. Degrees lie in `ℕ∞`, retaining any infinite-codimension component.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical

universe u

namespace Variety

variable {k : Type u} [Field k] {X : Variety k}

namespace Cycle

/-- Keep precisely the coefficients of the chosen codimension, as an additive projection. -/
def component (X : Variety k) (d : ℕ∞) : X.Cycle →+ X.Cycle where
  toFun c :=
    { toFun := fun x => if generatorCodimension x = d then c x else 0
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro x _hx
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        apply c.finite_support.subset
        intro y hy
        by_contra hcy
        have hz : c y = 0 := by simpa only [Function.mem_support, not_not] using hcy
        simp [hz] at hy }
  map_zero' := by
    apply Cycle.ext
    intro x
    change (if generatorCodimension x = d then (0 : X.Cycle) x else 0) = 0
    simp
  map_add' c e := by
    apply Cycle.ext
    intro x
    change (if generatorCodimension x = d then c x + e x else 0) =
      (if generatorCodimension x = d then c x else 0) +
        (if generatorCodimension x = d then e x else 0)
    split_ifs <;> simp

@[simp]
lemma component_apply (d : ℕ∞) (c : X.Cycle) (x : X.toScheme) :
    component X d c x = if generatorCodimension x = d then c x else 0 := rfl

/-- A finite component belongs to the corresponding fixed-codimension subgroup. -/
lemma component_mem_codimensionCycles (p : ℕ) (c : X.Cycle) :
    component X (p : ℕ∞) c ∈ codimensionCycles X p := by
  intro x hx
  simp [hx]

/-- A cycle already supported in degree `p` is fixed by its degree-`p` projection. -/
lemma component_eq_self_of_mem {p : ℕ} {c : X.Cycle}
    (hc : c ∈ codimensionCycles X p) : component X (p : ℕ∞) c = c := by
  apply Cycle.ext
  intro x
  by_cases hx : generatorCodimension x = (p : ℕ∞)
  · simp [hx]
  · simp [hx, hc x hx]

/-- Selecting the same component twice is idempotent. -/
@[simp]
lemma component_idem (d : ℕ∞) (c : X.Cycle) :
    component X d (component X d c) = component X d c := by
  apply Cycle.ext
  intro x
  by_cases hx : generatorCodimension x = d <;> simp [hx]

/-- Projections onto distinct degrees annihilate one another. -/
lemma component_component_of_ne {d e : ℕ∞} (hde : d ≠ e) (c : X.Cycle) :
    component X d (component X e c) = 0 := by
  apply Cycle.ext
  intro x
  by_cases hx : generatorCodimension x = d
  · have hxe : generatorCodimension x ≠ e := by
      intro h
      exact hde (hx.symm.trans h)
    simp [hx, hxe]
  · simp [hx]

/-- Components preserve effectivity because they only discard coefficients. -/
lemma IsEffective.component {c : X.Cycle} (hc : IsEffective c) (d : ℕ∞) :
    IsEffective (component X d c) := by
  intro x
  simp only [component_apply]
  split_ifs
  · exact hc x
  · exact le_rfl

/-- Only the degrees of the finitely many nonzero coefficients are needed for reconstruction. -/
def degrees (c : X.Cycle) : Finset ℕ∞ :=
  c.finite_support.toFinset.image generatorCodimension

/-- Every cycle is the finite sum of its components, including degree infinity when present. -/
lemma sum_components (c : X.Cycle) :
    ∑ d ∈ c.degrees, component X d c = c := by
  apply Cycle.ext
  intro x
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply, component_apply]
  by_cases hx : c x = 0
  · simp [hx]
  · have hm : generatorCodimension x ∈ c.degrees := by
      apply Finset.mem_image.mpr
      exact ⟨x, by simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hx, rfl⟩
    simp [hm]

end Cycle

end Variety

end

end LeanVarieties
