import LeanVarieties.CycleComponents

/-!
# Uniqueness of homogeneous cycle decompositions

A cycle is homogeneous of degree `d : ℕ∞` when projection to that degree fixes
it. Finite sums of homogeneous cycles have uniquely recoverable summands.
-/

namespace LeanVarieties

noncomputable section

open scoped Classical

universe u

namespace Variety

variable {k : Type u} [Field k] {X : Variety k}

namespace Cycle

/-- A homogeneous cycle is fixed by the projection to its degree. -/
def IsHomogeneous (d : ℕ∞) (c : X.Cycle) : Prop :=
  component X d c = c

lemma isHomogeneous_component (d : ℕ∞) (c : X.Cycle) :
    IsHomogeneous d (component X d c) :=
  component_idem d c

/-- For finite degrees, homogeneity is precisely membership in the codimension subgroup. -/
lemma isHomogeneous_iff_mem_codimensionCycles (p : ℕ) (c : X.Cycle) :
    IsHomogeneous (p : ℕ∞) c ↔ c ∈ codimensionCycles X p := by
  constructor
  · intro hc
    rw [← hc]
    exact component_mem_codimensionCycles p c
  · exact component_eq_self_of_mem

/-- A homogeneous cycle has zero projection to every other degree. -/
lemma IsHomogeneous.component_eq_zero {d e : ℕ∞} {c : X.Cycle}
    (hc : IsHomogeneous e c) (hde : d ≠ e) : component X d c = 0 := by
  rw [← hc]
  exact component_component_of_ne hde c

/-- Equality of cycles can be checked component by component. -/
lemma ext_of_components {c e : X.Cycle}
    (h : ∀ d : ℕ∞, component X d c = component X d e) : c = e := by
  apply Cycle.ext
  intro x
  have hx := congrArg (fun z : X.Cycle => z x) (h (generatorCodimension x))
  simpa using hx

/-- Effectivity can be checked independently in every degree. -/
lemma isEffective_iff_components (c : X.Cycle) :
    IsEffective c ↔ ∀ d : ℕ∞, IsEffective (component X d c) := by
  constructor
  · intro hc d
    exact hc.component d
  · intro h x
    have hx := h (generatorCodimension x) x
    simpa using hx

/-- Projection recovers the matching summand of a finite homogeneous sum. -/
lemma component_sum_homogeneous (s : Finset ℕ∞) (f : ℕ∞ → X.Cycle)
    (hf : ∀ e ∈ s, IsHomogeneous e (f e)) (d : ℕ∞) :
    component X d (∑ e ∈ s, f e) = if d ∈ s then f d else 0 := by
  rw [map_sum]
  by_cases hd : d ∈ s
  · simp only [hd, ite_true]
    calc
      ∑ e ∈ s, component X d (f e) = component X d (f d) := by
        apply Finset.sum_eq_single d
        · intro e he hed
          exact (hf e he).component_eq_zero (Ne.symm hed)
        · intro hds
          exact (hds hd).elim
      _ = f d := hf d hd
  · simp only [hd, ite_false]
    apply Finset.sum_eq_zero
    intro e he
    apply (hf e he).component_eq_zero
    intro hde
    exact hd (hde.symm ▸ he)

/-- In a homogeneous decomposition of `c`, each listed term is its canonical component. -/
lemma homogeneous_summand_eq_component (s : Finset ℕ∞) (f : ℕ∞ → X.Cycle)
    (hf : ∀ e ∈ s, IsHomogeneous e (f e)) {c : X.Cycle}
    (hc : ∑ e ∈ s, f e = c) {d : ℕ∞} (hd : d ∈ s) : f d = component X d c := by
  have h := congrArg (component X d) hc
  rw [component_sum_homogeneous s f hf d] at h
  simpa only [hd, ite_true] using h

/-- Two homogeneous sums over the same finite set are equal exactly when their terms agree. -/
lemma sum_homogeneous_eq_iff (s : Finset ℕ∞) (f g : ℕ∞ → X.Cycle)
    (hf : ∀ e ∈ s, IsHomogeneous e (f e)) (hg : ∀ e ∈ s, IsHomogeneous e (g e)) :
    (∑ e ∈ s, f e) = (∑ e ∈ s, g e) ↔ ∀ e ∈ s, f e = g e := by
  constructor
  · intro h d hd
    have hp := congrArg (component X d) h
    simpa only [component_sum_homogeneous s f hf d,
      component_sum_homogeneous s g hg d, hd, ite_true] using hp
  · intro h
    exact Finset.sum_congr rfl h

end Cycle

end Variety

end

end LeanVarieties
