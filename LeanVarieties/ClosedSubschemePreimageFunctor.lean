import LeanVarieties.ClosedSubschemePreimageIntersection

/-!
# Functorial inverse images of closed subschemes

Inverse images and their inclusion maps form a functor on the opposite ideal
poset. The restricted maps to the original closed subschemes are natural, and
inverse image along the identity is naturally isomorphic to the original
closed-subscheme functor.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k] {X Y : Variety k}

/-- Inverse-image inclusions preserve identity maps. -/
@[simp]
lemma closedSubschemePreimageInclusion_id (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    closedSubschemePreimageInclusion f (le_refl I) = 𝟙 (closedSubschemePreimage f I) := by
  apply closedSubschemePreimage_hom_ext f I
  simp

/-- Inverse-image inclusions preserve composition. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageInclusion_comp (f : X ⟶ Y)
    {I J K : Y.toScheme.IdealSheafData} (hIJ : I ≤ J) (hJK : J ≤ K) :
    closedSubschemePreimageInclusion f hJK ≫ closedSubschemePreimageInclusion f hIJ =
      closedSubschemePreimageInclusion f (hIJ.trans hJK) := by
  apply closedSubschemePreimage_hom_ext f I
  simp

/-- Inverse images of closed subschemes, contravariant in their defining ideals. -/
def closedSubschemePreimageFunctor (f : X ⟶ Y) :
    (Y.toScheme.IdealSheafData)ᵒᵖ ⥤ Variety k where
  obj I := closedSubschemePreimage f I.unop
  map a := closedSubschemePreimageInclusion f a.unop.le
  map_id I := closedSubschemePreimageInclusion_id f I.unop
  map_comp a b := (closedSubschemePreimageInclusion_comp f b.unop.le a.unop.le).symm

/-- Restriction to the original closed subschemes is natural in the ideal. -/
def closedSubschemePreimageRestriction (f : X ⟶ Y) :
    closedSubschemePreimageFunctor f ⟶ closedSubschemeFunctor Y where
  app I := closedSubschemePreimageMap f I.unop
  naturality := by
    intro I J a
    exact closedSubschemePreimageInclusion_map f a.unop.le

@[simp]
lemma closedSubschemePreimageRestriction_app (f : X ⟶ Y)
    (I : (Y.toScheme.IdealSheafData)ᵒᵖ) :
    (closedSubschemePreimageRestriction f).app I = closedSubschemePreimageMap f I.unop := rfl

/-- The identity comparison is natural with respect to closed-subscheme inclusions. -/
def closedSubschemePreimageIdNatIso (X : Variety k) :
    closedSubschemePreimageFunctor (𝟙 X) ≅ closedSubschemeFunctor X :=
  NatIso.ofComponents (fun I => closedSubschemePreimageIdIso X I.unop) (by
    intro I J a
    change closedSubschemePreimageInclusion (𝟙 X) a.unop.le ≫
      (closedSubschemePreimageIdIso X J.unop).hom =
        (closedSubschemePreimageIdIso X I.unop).hom ≫ closedSubschemeInclusion X a.unop.le
    rw [closedSubschemePreimageIdIso_hom, closedSubschemePreimageIdIso_hom]
    exact closedSubschemePreimageInclusion_map (𝟙 X) a.unop.le)

@[simp]
lemma closedSubschemePreimageIdNatIso_hom_app (X : Variety k)
    (I : (X.toScheme.IdealSheafData)ᵒᵖ) :
    (closedSubschemePreimageIdNatIso X).hom.app I =
      (closedSubschemePreimageIdIso X I.unop).hom := rfl

@[simp]
lemma closedSubschemePreimageIdNatIso_inv_app (X : Variety k)
    (I : (X.toScheme.IdealSheafData)ᵒᵖ) :
    (closedSubschemePreimageIdNatIso X).inv.app I =
      (closedSubschemePreimageIdIso X I.unop).inv := rfl

/-- The natural identity comparison has the canonical restriction transformation as its hom. -/
lemma closedSubschemePreimageIdNatIso_hom (X : Variety k) :
    (closedSubschemePreimageIdNatIso X).hom = closedSubschemePreimageRestriction (𝟙 X) := by
  ext I
  exact closedSubschemePreimageIdIso_hom X I.unop

end Variety

end

end LeanVarieties
