import LeanVarieties.CycleComponents
import LeanVarieties.CycleSupport

/-!
# Canonical effective decomposition of cycles

Reuse mathlib's lattice positive and negative parts. Every integer cycle is a
difference of effective cycles with disjoint coefficient supports, uniquely so.
The closed geometric supports may intersect along specializations.
-/

namespace LeanVarieties

noncomputable section

universe u

namespace Variety.Cycle

variable {k : Type u} [Field k] {X : Variety k}

/-- The pointwise effectivity predicate is the inherited order's nonnegativity. -/
lemma isEffective_iff_nonneg (c : X.Cycle) : IsEffective c ↔ 0 ≤ c := Iff.rfl

/-- The positive part is effective. -/
lemma isEffective_posPart (c : X.Cycle) : IsEffective c⁺ := by
  intro x
  exact posPart_nonneg (c x)

/-- The negative part is also effective: its coefficients are nonnegative magnitudes. -/
lemma isEffective_negPart (c : X.Cycle) : IsEffective c⁻ := by
  intro x
  exact negPart_nonneg (c x)

/-- Splitting signs partitions the nonzero generic-point coefficients. -/
lemma support_eq_union_parts (c : X.Cycle) :
    Function.support c = Function.support c⁺ ∪ Function.support c⁻ := by
  ext x
  change c x ≠ 0 ↔ max (c x) 0 ≠ 0 ∨ max (-c x) 0 ≠ 0
  omega

/-- No irreducible generator occurs in both effective parts. -/
lemma disjoint_support_parts (c : X.Cycle) :
    Disjoint (Function.support c⁺) (Function.support c⁻) := by
  apply Set.disjoint_left.mpr
  intro x hp hn
  change max (c x) 0 ≠ 0 at hp
  change max (-c x) 0 ≠ 0 at hn
  omega

/-- Every integer cycle is a difference of effective cycles with disjoint coefficients. -/
lemma exists_effective_sub (c : X.Cycle) :
    ∃ a b : X.Cycle, IsEffective a ∧ IsEffective b ∧
      Disjoint (Function.support a) (Function.support b) ∧ c = a - b :=
  ⟨c⁺, c⁻, isEffective_posPart c, isEffective_negPart c,
    disjoint_support_parts c, (posPart_sub_negPart c).symm⟩

/-- A disjoint effective presentation must be the canonical positive and negative parts. -/
lemma effective_sub_parts {a b : X.Cycle} (ha : IsEffective a) (hb : IsEffective b)
    (hd : Disjoint (Function.support a) (Function.support b)) :
    (a - b)⁺ = a ∧ (a - b)⁻ = b := by
  have hzero (x : X.toScheme) : a x = 0 ∨ b x = 0 := by
    by_cases hx : a x = 0
    · exact Or.inl hx
    · right
      by_contra hy
      exact Set.disjoint_left.mp hd hx hy
  constructor
  · apply ext
    intro x
    have hax := ha x
    have hbx := hb x
    have hz := hzero x
    change max (a x - b x) 0 = a x
    omega
  · apply ext
    intro x
    have hax := ha x
    have hbx := hb x
    have hz := hzero x
    change max (-(a x - b x)) 0 = b x
    omega

/-- In particular, a disjoint effective decomposition of a specified cycle is unique. -/
lemma effective_decomposition_unique {c a b : X.Cycle}
    (ha : IsEffective a) (hb : IsEffective b)
    (hd : Disjoint (Function.support a) (Function.support b)) (h : c = a - b) :
    a = c⁺ ∧ b = c⁻ := by
  rw [h]
  exact ⟨(effective_sub_parts ha hb hd).1.symm, (effective_sub_parts ha hb hd).2.symm⟩

/-- The geometric support is the union of the two effective parts' closed supports. -/
lemma geometricSupport_eq_sup_parts (c : X.Cycle) :
    geometricSupport c = geometricSupport c⁺ ⊔ geometricSupport c⁻ := by
  apply SetLike.coe_injective
  change closure (Function.support c) =
    closure (Function.support c⁺) ∪ closure (Function.support c⁻)
  rw [support_eq_union_parts, closure_union]

/-- Taking a codimension component commutes with taking the positive part. -/
@[simp]
lemma component_posPart (d : ℕ∞) (c : X.Cycle) :
    component X d c⁺ = (component X d c)⁺ := by
  apply ext
  intro x
  by_cases hx : generatorCodimension x = d <;> simp [component_apply, hx]

/-- Taking a codimension component commutes with taking the negative part. -/
@[simp]
lemma component_negPart (d : ℕ∞) (c : X.Cycle) :
    component X d c⁻ = (component X d c)⁻ := by
  apply ext
  intro x
  by_cases hx : generatorCodimension x = d <;> simp [component_apply, hx]

/-- Both effective parts of a codimension-`p` cycle remain in codimension `p`. -/
lemma parts_mem_codimensionCycles {p : ℕ} {c : X.Cycle}
    (hc : c ∈ codimensionCycles X p) :
    c⁺ ∈ codimensionCycles X p ∧ c⁻ ∈ codimensionCycles X p := by
  constructor
  · intro x hx
    change (c x)⁺ = 0
    rw [hc x hx]
    simp
  · intro x hx
    change (c x)⁻ = 0
    rw [hc x hx]
    simp

end Variety.Cycle

end

end LeanVarieties
