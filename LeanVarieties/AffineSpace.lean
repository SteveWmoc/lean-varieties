import LeanVarieties.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Affine space as a variety

This file provides the first standard example for the varieties API: affine
`n`-space over a field `k`.

Mathlib indexes affine-space coordinates by a type in the same universe as the
base scheme. For a natural-number dimension `n`, we therefore use
`ULift (Fin n)` as the coordinate index type.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- The underlying scheme of affine `n`-space over `k`. -/
abbrev affineScheme (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) (baseScheme k)

/-- Affine `n`-space over `k`, regarded as a variety over `k`. -/
def affineSpace (n : ℕ) : Variety k :=
  ofScheme (affineScheme k n) ((affineScheme k n) ↘ baseScheme k)

@[simp]
lemma affineSpace_toScheme (n : ℕ) :
    (affineSpace (k := k) n).toScheme = affineScheme k n := rfl

@[simp]
lemma affineSpace_structureMap (n : ℕ) :
    (affineSpace (k := k) n).structureMap =
      ((affineScheme k n) ↘ baseScheme k) := rfl

instance (n : ℕ) : IsAffineHom (affineSpace (k := k) n).structureMap := by
  change IsAffineHom ((affineScheme k n) ↘ baseScheme k)
  infer_instance

instance (n : ℕ) : LocallyOfFinitePresentation (affineSpace (k := k) n).structureMap := by
  change LocallyOfFinitePresentation ((affineScheme k n) ↘ baseScheme k)
  infer_instance

end Variety

end

end LeanVarieties
