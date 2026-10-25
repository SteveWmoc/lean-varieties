import LeanVarieties.AlgebraicCycle
import Mathlib.Topology.KrullDimension

/-!
# Cycles supported in a fixed codimension

Codimension is the coheight of a generator's irreducible closed closure in the
inclusion poset of irreducible closed subsets. It takes values in `ℕ∞` without
truncating infinite values. Cycles of a fixed finite codimension form a subgroup.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical

universe u

namespace Variety

variable {k : Type u} [Field k] {X : Variety k}

namespace Cycle

/-- The irreducible closed subset indexed by a cycle's generic point. -/
def generatorClosed (x : X.toScheme) : TopologicalSpace.IrreducibleCloseds X.toScheme :=
  ⟨generatorCarrier x, generatorCarrier_isIrreducible x, (generatorCarrier x).isClosed⟩

/-- Codimension of the irreducible closure, measured by chains of irreducible closed supersets. -/
def generatorCodimension (x : X.toScheme) : ℕ∞ :=
  Order.coheight (generatorClosed x)

/-- Cycles whose nonzero coefficients lie in the specified set of generic points. -/
def supportedOn (X : Variety k) (S : Set X.toScheme) : AddSubgroup X.Cycle where
  carrier := {c | ∀ x, x ∉ S → c x = 0}
  zero_mem' := by
    intro x _hx
    rfl
  add_mem' := by
    intro c d hc hd x hx
    change c x + d x = 0
    rw [hc x hx, hd x hx, add_zero]
  neg_mem' := by
    intro c hc x hx
    change -c x = 0
    rw [hc x hx, neg_zero]

@[simp]
lemma mem_supportedOn (S : Set X.toScheme) (c : X.Cycle) :
    c ∈ supportedOn X S ↔ ∀ x, x ∉ S → c x = 0 := Iff.rfl

lemma mem_supportedOn_iff_support_subset (S : Set X.toScheme) (c : X.Cycle) :
    c ∈ supportedOn X S ↔ Function.support c ⊆ S := by
  constructor
  · intro h x hx
    by_contra hxs
    exact hx (h x hxs)
  · intro h x hx
    by_contra hcx
    exact hx (h hcx)

lemma single_mem_supportedOn (S : Set X.toScheme) (x : X.toScheme) (n : ℤ)
    (hx : x ∈ S) : single x n ∈ supportedOn X S := by
  intro y hy
  have hne : y ≠ x := by
    intro h
    exact hy (h.symm ▸ hx)
  simp [hne]

lemma single_one_mem_supportedOn_iff (S : Set X.toScheme) (x : X.toScheme) :
    single x 1 ∈ supportedOn X S ↔ x ∈ S := by
  constructor
  · intro h
    by_contra hx
    have hz := h x hx
    simp at hz
  · exact single_mem_supportedOn S x 1

end Cycle

/-- Integer cycles supported in codimension `p`, as a subgroup of all cycles. -/
def codimensionCycles (X : Variety k) (p : ℕ) : AddSubgroup X.Cycle :=
  Cycle.supportedOn X {x | Cycle.generatorCodimension x = (p : ℕ∞)}

@[simp]
lemma mem_codimensionCycles (p : ℕ) (c : X.Cycle) :
    c ∈ codimensionCycles X p ↔
      ∀ x, Cycle.generatorCodimension x ≠ (p : ℕ∞) → c x = 0 := Iff.rfl

/-- A generator with coefficient one has degree `p` precisely when its closure has codimension `p`. -/
@[simp]
lemma single_one_mem_codimensionCycles_iff (p : ℕ) (x : X.toScheme) :
    Cycle.single x 1 ∈ codimensionCycles X p ↔
      Cycle.generatorCodimension x = (p : ℕ∞) :=
  Cycle.single_one_mem_supportedOn_iff _ x

/-- Different finite codimensions have no nonzero cycle in common. -/
lemma eq_zero_of_mem_codimensionCycles_of_ne {p q : ℕ} (hpq : p ≠ q)
    {c : X.Cycle} (hp : c ∈ codimensionCycles X p) (hq : c ∈ codimensionCycles X q) : c = 0 := by
  apply Cycle.ext
  intro x
  by_cases hx : Cycle.generatorCodimension x = (p : ℕ∞)
  · apply hq x
    intro hxq
    have hcast : (p : ℕ∞) = (q : ℕ∞) := hx.symm.trans hxq
    exact hpq (by exact_mod_cast hcast)
  · exact hp x hx

end Variety

end

end LeanVarieties
