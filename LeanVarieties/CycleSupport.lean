import LeanVarieties.CycleCodimension

/-!
# Geometric support of algebraic cycles

The closed support is the finite union of the irreducible closed subsets with
nonzero coefficients. Effective addition has no cancellation of support.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical

universe u

namespace Variety.Cycle

variable {k : Type u} [Field k] {X : Variety k}

/-- The closed geometric support, including specializations of generic points. -/
def geometricSupport (c : X.Cycle) : TopologicalSpace.Closeds X.toScheme :=
  ⟨closure (Function.support c), isClosed_closure⟩

/-- Geometric support is the finite union of the nonzero generators' closures. -/
lemma geometricSupport_eq_iUnion (c : X.Cycle) :
    (geometricSupport c : Set X.toScheme) =
      ⋃ x ∈ Function.support c, (generatorCarrier x : Set X.toScheme) := by
  change closure (Function.support c) = ⋃ x ∈ Function.support c, closure ({x} : Set X.toScheme)
  rw [← c.finite_support.closure_biUnion]
  congr 1
  ext x
  simp

/-- Support lies in a closed set exactly when all coefficients outside it vanish. -/
lemma geometricSupport_le_iff (c : X.Cycle) (Z : TopologicalSpace.Closeds X.toScheme) :
    geometricSupport c ≤ Z ↔ c ∈ supportedOn X (Z : Set X.toScheme) := by
  change closure (Function.support c) ⊆ (Z : Set X.toScheme) ↔ _
  rw [mem_supportedOn_iff_support_subset]
  exact ⟨fun h => subset_closure.trans h, fun h => closure_minimal h Z.isClosed⟩

@[simp]
lemma geometricSupport_zero : geometricSupport (0 : X.Cycle) = ⊥ := by
  apply SetLike.coe_injective
  simp [geometricSupport, Function.support]

/-- A cycle has empty geometric support precisely when it vanishes. -/
@[simp]
lemma geometricSupport_eq_bot_iff (c : X.Cycle) : geometricSupport c = ⊥ ↔ c = 0 := by
  constructor
  · intro h
    apply ext
    intro x
    by_contra hx
    have hm : x ∈ (geometricSupport c : Set X.toScheme) := subset_closure hx
    rw [h] at hm
    exact hm
  · rintro rfl
    exact geometricSupport_zero

/-- Cancellation can only shrink the support of a sum. -/
lemma geometricSupport_add_le (c e : X.Cycle) :
    geometricSupport (c + e) ≤ geometricSupport c ⊔ geometricSupport e := by
  apply (geometricSupport_le_iff _ _).mpr
  intro x hx
  have hc : c x = 0 := by
    by_contra h
    exact hx (Or.inl (subset_closure h))
  have he : e x = 0 := by
    by_contra h
    exact hx (Or.inr (subset_closure h))
  change c x + e x = 0
  rw [hc, he, add_zero]

/-- Effective cycles cannot cancel each other's nonzero coefficients. -/
lemma IsEffective.support_add {c e : X.Cycle} (hc : IsEffective c) (he : IsEffective e) :
    Function.support (c + e) = Function.support c ∪ Function.support e := by
  ext x
  change c x + e x ≠ 0 ↔ c x ≠ 0 ∨ e x ≠ 0
  have hcx := hc x
  have hex := he x
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact h (by rw [hn.1, hn.2, add_zero])
  · intro h hz
    rcases h with h | h <;> omega

/-- The geometric support of an effective sum is exactly the union of supports. -/
lemma IsEffective.geometricSupport_add {c e : X.Cycle}
    (hc : IsEffective c) (he : IsEffective e) :
    geometricSupport (c + e) = geometricSupport c ⊔ geometricSupport e := by
  apply SetLike.coe_injective
  change closure (Function.support (c + e)) =
    closure (Function.support c) ∪ closure (Function.support e)
  rw [hc.support_add he, closure_union]

end Variety.Cycle

end

end LeanVarieties
