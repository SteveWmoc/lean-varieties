import LeanVarieties.ClosedSubschemeInclusions
import LeanVarieties.Isomorphism

/-!
# The closed subscheme defined by the zero ideal

The canonical inclusion of a closed subscheme is an isomorphism exactly when
its ideal sheaf is zero. The zero ideal therefore recovers the ambient variety
over its base field, with its geometric properties and canonical inclusions.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- The canonical closed-subscheme inclusion is an isomorphism precisely for
the zero ideal. -/
@[simp]
lemma isIso_closedSubschemeι_iff_eq_bot (Y : Variety k)
    (I : Y.toScheme.IdealSheafData) : IsIso (closedSubschemeι Y I) ↔ I = ⊥ := by
  rw [← isIso_iff_of_reflects_iso (closedSubschemeι Y I) (forget k)]
  change IsIso I.subschemeι ↔ I = ⊥
  exact Scheme.isIso_subschemeι_iff_eq_bot I

instance closedSubschemeι_bot_isIso (Y : Variety k) :
    IsIso (closedSubschemeι Y ⊥) :=
  (isIso_closedSubschemeι_iff_eq_bot Y ⊥).2 rfl

/-- The zero ideal defines the whole ambient variety, canonically over `k`. -/
def closedSubschemeBotIso (Y : Variety k) : closedSubscheme Y ⊥ ≅ Y :=
  asIso (closedSubschemeι Y ⊥)

@[simp]
lemma closedSubschemeBotIso_hom (Y : Variety k) :
    (closedSubschemeBotIso Y).hom = closedSubschemeι Y ⊥ := rfl

@[simp]
lemma closedSubschemeBotIso_inv_hom_left (Y : Variety k) :
    (closedSubschemeBotIso Y).inv.hom.left =
      inv (Scheme.IdealSheafData.subschemeι (⊥ : Y.toScheme.IdealSheafData)) := by
  have : IsIso (Scheme.IdealSheafData.subschemeι (⊥ : Y.toScheme.IdealSheafData)) :=
    (Scheme.isIso_subschemeι_iff_eq_bot (⊥ : Y.toScheme.IdealSheafData)).2 rfl
  apply IsIso.eq_inv_of_hom_inv_id
  exact (forget k).congr_map (closedSubschemeBotIso Y).hom_inv_id

@[reassoc (attr := simp)]
lemma closedSubschemeBotIso_inv_structureMap (Y : Variety k) :
    (closedSubschemeBotIso Y).inv.hom.left ≫
      (closedSubscheme Y ⊥).structureMap = Y.structureMap :=
  Over.w (closedSubschemeBotIso Y).inv.hom

/-- Inclusion into the zero-ideal subscheme is the ambient inclusion followed
by the inverse of the canonical ambient isomorphism. -/
lemma closedSubschemeInclusion_bot (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    closedSubschemeInclusion Y (bot_le : ⊥ ≤ I) =
      closedSubschemeι Y I ≫ (closedSubschemeBotIso Y).inv := by
  apply (cancel_mono (closedSubschemeBotIso Y).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, closedSubschemeBotIso_hom]
  exact closedSubschemeInclusion_ι Y (bot_le : ⊥ ≤ I)

/-- The zero-ideal subscheme of a smooth variety is smooth. -/
instance closedSubscheme_bot_isSmooth (Y : Variety k) [Y.IsSmooth] :
    (closedSubscheme Y ⊥).IsSmooth :=
  isSmooth_of_iso (closedSubschemeBotIso Y)

/-- The zero-ideal subscheme of a proper variety is proper. -/
instance closedSubscheme_bot_isProper (Y : Variety k) [Y.IsProper] :
    (closedSubscheme Y ⊥).IsProper :=
  isProper_of_iso (closedSubschemeBotIso Y)

/-- The zero-ideal subscheme retains the ambient smooth relative dimension. -/
instance closedSubscheme_bot_isSmoothOfDimension (Y : Variety k) (n : ℕ)
    [Y.IsSmoothOfDimension n] : (closedSubscheme Y ⊥).IsSmoothOfDimension n :=
  isSmoothOfDimension_of_iso (closedSubschemeBotIso Y) n

end Variety

end

end LeanVarieties
