import LeanVarieties.Dimension

/-!
# Geometric properties under isomorphisms of varieties

An isomorphism in `Variety k` induces an isomorphism of underlying schemes
compatible with the structural morphisms. Smoothness, properness, projectivity,
and smoothness of fixed relative dimension can be transported along it.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k] {X Y : Variety k}

/-- The scheme isomorphism underlying an isomorphism of varieties. -/
abbrev schemeIso (e : X ≅ Y) : X.toScheme ≅ Y.toScheme :=
  (forget k).mapIso e

@[reassoc (attr := simp)]
lemma schemeIso_hom_structureMap (e : X ≅ Y) :
    (schemeIso e).hom ≫ Y.structureMap = X.structureMap :=
  Over.w e.hom.hom

/-- Transport smoothness from the target of a variety isomorphism. -/
lemma isSmooth_of_iso (e : X ≅ Y) [Y.IsSmooth] : X.IsSmooth := by
  change Smooth X.structureMap
  rw [← schemeIso_hom_structureMap e]
  infer_instance

/-- Transport properness from the target of a variety isomorphism. -/
lemma isProper_of_iso (e : X ≅ Y) [Y.IsProper] : X.IsProper := by
  change AlgebraicGeometry.IsProper X.structureMap
  rw [← schemeIso_hom_structureMap e]
  infer_instance

/-- Transport projectivity from the target of a variety isomorphism. -/
lemma isProjective_of_iso (e : X ≅ Y) [Y.IsProjective] : X.IsProjective :=
  IsProjective.of_closedImmersion (schemeIso e).hom (schemeIso_hom_structureMap e)

/-- Transport a fixed smooth dimension from the target of a variety isomorphism. -/
lemma isSmoothOfDimension_of_iso (e : X ≅ Y) (n : ℕ)
    [Y.IsSmoothOfDimension n] : X.IsSmoothOfDimension n := by
  change SmoothOfRelativeDimension n X.structureMap
  rw [← schemeIso_hom_structureMap e]
  simpa only [zero_add] using
    (smoothOfRelativeDimension_comp 0 n (schemeIso e).hom Y.structureMap)

/-- Isomorphic varieties have the same smoothness property. -/
lemma isSmooth_iff_of_iso (e : X ≅ Y) : X.IsSmooth ↔ Y.IsSmooth := by
  constructor
  · intro h
    have : X.IsSmooth := h
    exact isSmooth_of_iso e.symm
  · intro h
    have : Y.IsSmooth := h
    exact isSmooth_of_iso e

/-- Isomorphic varieties have the same properness property. -/
lemma isProper_iff_of_iso (e : X ≅ Y) : X.IsProper ↔ Y.IsProper := by
  constructor
  · intro h
    have : X.IsProper := h
    exact isProper_of_iso e.symm
  · intro h
    have : Y.IsProper := h
    exact isProper_of_iso e

/-- Isomorphic varieties have the same projectivity property. -/
lemma isProjective_iff_of_iso (e : X ≅ Y) : X.IsProjective ↔ Y.IsProjective := by
  constructor
  · intro h
    have : X.IsProjective := h
    exact isProjective_of_iso e.symm
  · intro h
    have : Y.IsProjective := h
    exact isProjective_of_iso e

/-- Isomorphic varieties have the same fixed smooth relative dimension. -/
lemma isSmoothOfDimension_iff_of_iso (e : X ≅ Y) (n : ℕ) :
    X.IsSmoothOfDimension n ↔ Y.IsSmoothOfDimension n := by
  constructor
  · intro h
    have : X.IsSmoothOfDimension n := h
    exact isSmoothOfDimension_of_iso e.symm n
  · intro h
    have : Y.IsSmoothOfDimension n := h
    exact isSmoothOfDimension_of_iso e n

end Variety

end

end LeanVarieties
