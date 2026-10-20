import LeanVarieties.Basic
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Algebraic cycles on varieties

Reuse mathlib's generic-point presentation of algebraic cycles. On a variety,
local finiteness implies finite support because the underlying scheme is
quasi-compact. These cycles are ungraded: no codimension condition is imposed.
-/

namespace LeanVarieties

noncomputable section

open AlgebraicGeometry

open scoped Classical

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Integer algebraic cycles, indexed by generic points of irreducible closed subsets. -/
abbrev Cycle (X : Variety k) :=
  AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ

namespace Cycle

variable {X : Variety k}

/-- Cycles are determined by all their coefficients. -/
@[ext]
lemma ext {c d : X.Cycle} (h : ∀ x, c x = d x) : c = d :=
  Function.locallyFinsuppWithin.ext h

/-- A variety is quasi-compact, so every cycle has only finitely many nonzero coefficients. -/
lemma finite_support (c : X.Cycle) : (Function.support c).Finite := by
  have : CompactSpace X.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace X.structureMap
  simpa only [Set.univ_inter, Function.locallyFinsuppWithin.toFun_eq_coe] using
    c.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

/-- A cycle with one specified coefficient at a generic point. -/
def single (x : X.toScheme) (n : ℤ) : X.Cycle := by
  classical
  exact Function.locallyFinsuppWithin.single x n

@[simp]
lemma single_apply (x y : X.toScheme) (n : ℤ) :
    single x n y = if y = x then n else 0 := by
  classical
  exact Function.locallyFinsuppWithin.single_apply

@[simp]
lemma single_zero (x : X.toScheme) : single x 0 = 0 := by
  apply ext
  intro y
  simp

/-- Every cycle is the finite sum of its nonzero generic-point coefficients. -/
lemma sum_single (c : X.Cycle) :
    ∑ x ∈ c.finite_support.toFinset, single x (c x) = c := by
  classical
  exact Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ c.finite_support

/-- The closed subset represented by a generic-point generator. -/
def generatorCarrier (x : X.toScheme) : TopologicalSpace.Closeds X.toScheme :=
  ⟨closure ({x} : Set X.toScheme), isClosed_closure⟩

/-- Each generic-point generator represents a nonempty irreducible closed subset. -/
lemma generatorCarrier_isIrreducible (x : X.toScheme) :
    IsIrreducible (generatorCarrier x : Set X.toScheme) :=
  isIrreducible_singleton.closure

/-- Effectivity means that all generic-point coefficients are nonnegative. -/
def IsEffective (c : X.Cycle) : Prop :=
  ∀ x, 0 ≤ c x

lemma isEffective_zero : IsEffective (0 : X.Cycle) := by
  intro x
  exact le_rfl

lemma IsEffective.add {c d : X.Cycle} (hc : IsEffective c) (hd : IsEffective d) :
    IsEffective (c + d) := by
  intro x
  exact add_nonneg (hc x) (hd x)

lemma isEffective_single (x : X.toScheme) {n : ℤ} (hn : 0 ≤ n) :
    IsEffective (single x n) := by
  intro y
  classical
  simp only [single_apply]
  split_ifs
  · exact hn
  · exact le_rfl

end Cycle

end Variety

end

end LeanVarieties
