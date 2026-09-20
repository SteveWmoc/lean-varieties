import LeanVarieties.Projective

/-!
# Smooth varieties of fixed relative dimension

For varieties over a field, the natural dimension datum for smooth objects is
the relative dimension of the structural morphism to `Spec k`. Mathlib
represents this by `SmoothOfRelativeDimension n`.

This file lifts that notion to the project's variety layer and packages smooth
varieties, and smooth projective varieties, of a fixed dimension as full
subcategories.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- A variety is smooth of dimension `n` over its base field when its structural
morphism is smooth of relative dimension `n`. -/
abbrev IsSmoothOfDimension (X : Variety k) (n : ℕ) : Prop :=
  SmoothOfRelativeDimension n X.structureMap

set_option linter.style.haveILetI false in
/-- Being smooth of dimension `n` implies smoothness. -/
lemma IsSmoothOfDimension.isSmooth {X : Variety k} {n : ℕ}
    (h : X.IsSmoothOfDimension n) : X.IsSmooth := by
  letI : SmoothOfRelativeDimension n X.structureMap := h
  exact SmoothOfRelativeDimension.smooth n X.structureMap

/-- Smoothness of fixed dimension as an object property on varieties. -/
def smoothOfDimensionProperty (k : Type u) [Field k] (n : ℕ) :
    ObjectProperty (Variety k) :=
  fun X => X.IsSmoothOfDimension n

/-- Smoothness of fixed dimension together with projectivity. -/
def smoothProjectiveOfDimensionProperty (k : Type u) [Field k] (n : ℕ) :
    ObjectProperty (Variety k) :=
  fun X => X.IsSmoothOfDimension n ∧ X.IsProjective

end Variety

/-- The full subcategory of smooth `n`-dimensional varieties over `k`. -/
abbrev SmoothVarietyOfDimension (k : Type u) [Field k] (n : ℕ) :=
  (Variety.smoothOfDimensionProperty k n).FullSubcategory

/-- The full subcategory of smooth projective `n`-dimensional varieties over `k`. -/
abbrev SmoothProjectiveVarietyOfDimension (k : Type u) [Field k] (n : ℕ) :=
  (Variety.smoothProjectiveOfDimensionProperty k n).FullSubcategory

namespace SmoothVarietyOfDimension

variable {k : Type u} [Field k] {n : ℕ}

instance isSmoothOfDimension (X : SmoothVarietyOfDimension k n) :
    X.obj.IsSmoothOfDimension n :=
  X.property

instance isSmooth (X : SmoothVarietyOfDimension k n) : X.obj.IsSmooth :=
  X.property.isSmooth

/-- Forget the fixed relative dimension while retaining smoothness. -/
def forgetDimension (k : Type u) [Field k] (n : ℕ) :
    SmoothVarietyOfDimension k n ⥤ SmoothVariety k :=
  ObjectProperty.ιOfLE (fun _ h => h.isSmooth)

end SmoothVarietyOfDimension

namespace SmoothProjectiveVarietyOfDimension

variable {k : Type u} [Field k] {n : ℕ}

instance isSmoothOfDimension (X : SmoothProjectiveVarietyOfDimension k n) :
    X.obj.IsSmoothOfDimension n :=
  X.property.1

instance isSmooth (X : SmoothProjectiveVarietyOfDimension k n) : X.obj.IsSmooth :=
  X.property.1.isSmooth

instance isProjective (X : SmoothProjectiveVarietyOfDimension k n) :
    X.obj.IsProjective :=
  X.property.2

/-- Forget the fixed relative dimension while retaining smoothness and projectivity. -/
def forgetDimension (k : Type u) [Field k] (n : ℕ) :
    SmoothProjectiveVarietyOfDimension k n ⥤ SmoothProjectiveVariety k :=
  ObjectProperty.ιOfLE (fun _ h => ⟨h.1.isSmooth, h.2⟩)

end SmoothProjectiveVarietyOfDimension

/-- Smooth complex algebraic varieties of fixed dimension. -/
abbrev SmoothComplexVarietyOfDimension (n : ℕ) :=
  SmoothVarietyOfDimension ℂ n

/-- Smooth projective complex algebraic varieties of fixed dimension. -/
abbrev SmoothProjectiveComplexVarietyOfDimension (n : ℕ) :=
  SmoothProjectiveVarietyOfDimension ℂ n

end

end LeanVarieties
