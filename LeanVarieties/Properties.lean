import LeanVarieties.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Data.Complex.Basic

/-!
# Geometric properties of varieties

This file lifts scheme-theoretic properties of the structural morphism to the
object level for `Variety k`.

No new mathematical notion is introduced: a variety is smooth (respectively
proper) exactly when its structural morphism to `Spec k` is smooth
(respectively proper) in mathlib's sense.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- A variety is smooth over its base field when its structural morphism is smooth. -/
abbrev IsSmooth (X : Variety k) : Prop :=
  AlgebraicGeometry.Smooth X.structureMap

/-- A variety is proper over its base field when its structural morphism is proper. -/
abbrev IsProper (X : Variety k) : Prop :=
  AlgebraicGeometry.IsProper X.structureMap

/-- Smoothness as an object property on `Variety k`. -/
def smoothProperty (k : Type u) [Field k] : ObjectProperty (Variety k) :=
  fun X => X.IsSmooth

/-- Properness as an object property on `Variety k`. -/
def properProperty (k : Type u) [Field k] : ObjectProperty (Variety k) :=
  fun X => X.IsProper

end Variety

/-- The full subcategory of smooth varieties over `k`. -/
abbrev SmoothVariety (k : Type u) [Field k] :=
  (Variety.smoothProperty k).FullSubcategory

/-- The full subcategory of proper varieties over `k`. -/
abbrev ProperVariety (k : Type u) [Field k] :=
  (Variety.properProperty k).FullSubcategory

/-- Complex algebraic varieties in the project's sense. -/
abbrev ComplexVariety := Variety ℂ

/-- Smooth complex algebraic varieties. -/
abbrev SmoothComplexVariety := SmoothVariety ℂ

/-- Proper complex algebraic varieties. -/
abbrev ProperComplexVariety := ProperVariety ℂ

end

end LeanVarieties
