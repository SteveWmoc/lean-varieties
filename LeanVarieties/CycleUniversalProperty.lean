import LeanVarieties.AlgebraicCycle
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# The universal property of integer cycles

On a variety, cycles are finitely supported integer coefficient functions.
An assignment on generic-point generators therefore extends uniquely to an
additive map into any abelian group.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical

universe u v

namespace Variety.Cycle

variable {k : Type u} [Field k] {X : Variety k}

/-- Quasi-compactness identifies cycles with finitely supported integer functions. -/
def coefficientsEquiv (X : Variety k) : X.Cycle ≃+ (X.toScheme →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite c c.finite_support
  invFun f :=
    { toFun := f
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro x _hx
        exact ⟨Set.univ, Filter.univ_mem, by simpa using f.finite_support⟩ }
  left_inv c := by
    apply ext
    intro x
    rfl
  right_inv f := by
    apply Finsupp.ext
    intro x
    rfl
  map_add' c e := by
    apply Finsupp.ext
    intro x
    rfl

@[simp]
lemma coefficientsEquiv_apply (c : X.Cycle) (x : X.toScheme) :
    coefficientsEquiv X c x = c x := rfl

@[simp]
lemma coefficientsEquiv_symm_apply (f : X.toScheme →₀ ℤ) (x : X.toScheme) :
    (coefficientsEquiv X).symm f x = f x := rfl

@[simp]
lemma coefficientsEquiv_single (x : X.toScheme) (n : ℤ) :
    coefficientsEquiv X (single x n) = Finsupp.single x n := by
  apply Finsupp.ext
  intro y
  simp [Finsupp.single_apply, eq_comm]

/-- Every coefficient multiple is an integer multiple of the unit generator. -/
lemma single_eq_zsmul (x : X.toScheme) (n : ℤ) :
    single x n = n • single x 1 := by
  apply ext
  intro y
  by_cases hy : y = x <;> simp [hy]

variable {A : Type v} [AddCommGroup A]

/-- Extend a generator assignment by integer linear combination of coefficients. -/
def lift (f : X.toScheme → A) : X.Cycle →+ A :=
  (Finsupp.liftAddHom fun x =>
    { toFun := fun n : ℤ => n • f x
      map_zero' := zero_zsmul _
      map_add' := fun m n => add_zsmul (f x) m n }).comp (coefficientsEquiv X).toAddMonoidHom

/-- The extension evaluates a cycle by its finite coefficient sum. -/
lemma lift_apply (f : X.toScheme → A) (c : X.Cycle) :
    lift f c = ∑ x ∈ c.finite_support.toFinset, (c x) • f x := rfl

@[simp]
lemma lift_single (f : X.toScheme → A) (x : X.toScheme) (n : ℤ) :
    lift f (single x n) = n • f x := by
  change Finsupp.liftAddHom _ (coefficientsEquiv X (single x n)) = _
  rw [coefficientsEquiv_single, Finsupp.liftAddHom_apply_single]

@[simp]
lemma lift_single_one (f : X.toScheme → A) (x : X.toScheme) :
    lift f (single x 1) = f x := by
  simp

/-- Additive maps on cycles are determined by unit generic-point generators. -/
lemma hom_ext {F G : X.Cycle →+ A}
    (h : ∀ x, F (single x 1) = G (single x 1)) : F = G := by
  apply AddMonoidHom.ext
  intro c
  rw [← sum_single c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [single_eq_zsmul, map_zsmul, map_zsmul, h x]

/-- The universal property: every generator assignment has exactly one additive extension. -/
lemma existsUnique_lift (f : X.toScheme → A) :
    ∃! F : X.Cycle →+ A, ∀ x, F (single x 1) = f x := by
  refine ⟨lift f, fun x => lift_single_one f x, ?_⟩
  intro F hF
  apply hom_ext
  intro x
  rw [hF x, lift_single_one]

/-- Extending an additive map's values on generators recovers that map. -/
@[simp]
lemma lift_generator_values (F : X.Cycle →+ A) :
    lift (fun x => F (single x 1)) = F := by
  apply hom_ext
  intro x
  exact lift_single_one _ x

end Variety.Cycle

end

end LeanVarieties
