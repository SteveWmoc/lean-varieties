import LeanVarieties.ClosedSubschemePreimageComposition

/-!
# Inverse images preserve scheme-theoretic intersections

The inverse image of an ideal sum is canonically isomorphic to the intersection
of the inverse images. The comparison respects the ambient inclusion and both
projections, including the maps back to the original closed subschemes.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k] {X Y : Variety k}

/-- Ideal inclusion induces an inclusion between inverse images. -/
def closedSubschemePreimageInclusion (f : X ⟶ Y)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    closedSubschemePreimage f J ⟶ closedSubschemePreimage f I :=
  closedSubschemeInclusion X (Scheme.IdealSheafData.comap_mono f.hom.left h)

@[reassoc (attr := simp)]
lemma closedSubschemePreimageInclusion_ι (f : X ⟶ Y)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    closedSubschemePreimageInclusion f h ≫ closedSubschemePreimageι f I =
      closedSubschemePreimageι f J :=
  closedSubschemeInclusion_ι X _

/-- The inclusion between inverse images commutes with the maps to the original subschemes. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageInclusion_map (f : X ⟶ Y)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    closedSubschemePreimageInclusion f h ≫ closedSubschemePreimageMap f I =
      closedSubschemePreimageMap f J ≫ closedSubschemeInclusion Y h := by
  apply closedSubscheme_hom_ext Y I
  rw [Category.assoc, closedSubschemePreimageMap_ι, ← Category.assoc,
    closedSubschemePreimageInclusion_ι, Category.assoc, closedSubschemeInclusion_ι,
    closedSubschemePreimageMap_ι]

/-- Scheme-theoretic inverse images preserve intersections, including their nilpotents. -/
def closedSubschemePreimageIntersectionIso (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    closedSubschemePreimage f (I ⊔ J) ≅
      closedSubschemeIntersection X (I.comap f.hom.left) (J.comap f.hom.left) :=
  closedSubschemeCongr X (Scheme.IdealSheafData.comap_sup I J f.hom.left)

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_hom_ι (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).hom ≫
      closedSubschemeι X (I.comap f.hom.left ⊔ J.comap f.hom.left) =
        closedSubschemePreimageι f (I ⊔ J) :=
  closedSubschemeCongr_hom_ι X _

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_inv_ι (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).inv ≫
      closedSubschemePreimageι f (I ⊔ J) =
        closedSubschemeι X (I.comap f.hom.left ⊔ J.comap f.hom.left) :=
  closedSubschemeCongr_inv_ι X _

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_hom_fst (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).hom ≫
      closedSubschemeIntersectionFst X (I.comap f.hom.left) (J.comap f.hom.left) =
        closedSubschemePreimageInclusion f (le_sup_left : I ≤ I ⊔ J) := by
  apply closedSubscheme_hom_ext X (I.comap f.hom.left)
  rw [Category.assoc, closedSubschemeIntersectionFst_ι,
    closedSubschemePreimageIntersectionIso_hom_ι]
  exact (closedSubschemePreimageInclusion_ι f (le_sup_left : I ≤ I ⊔ J)).symm

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_hom_snd (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).hom ≫
      closedSubschemeIntersectionSnd X (I.comap f.hom.left) (J.comap f.hom.left) =
        closedSubschemePreimageInclusion f (le_sup_right : J ≤ I ⊔ J) := by
  apply closedSubscheme_hom_ext X (J.comap f.hom.left)
  rw [Category.assoc, closedSubschemeIntersectionSnd_ι,
    closedSubschemePreimageIntersectionIso_hom_ι]
  exact (closedSubschemePreimageInclusion_ι f (le_sup_right : J ≤ I ⊔ J)).symm

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_inv_fst (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).inv ≫
      closedSubschemePreimageInclusion f (le_sup_left : I ≤ I ⊔ J) =
        closedSubschemeIntersectionFst X (I.comap f.hom.left) (J.comap f.hom.left) := by
  rw [← closedSubschemePreimageIntersectionIso_hom_fst, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_inv_snd (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageIntersectionIso f I J).inv ≫
      closedSubschemePreimageInclusion f (le_sup_right : J ≤ I ⊔ J) =
        closedSubschemeIntersectionSnd X (I.comap f.hom.left) (J.comap f.hom.left) := by
  rw [← closedSubschemePreimageIntersectionIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The first projection followed by restriction agrees with restriction then projection. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_hom_fst_map (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    ((closedSubschemePreimageIntersectionIso f I J).hom ≫
      closedSubschemeIntersectionFst X (I.comap f.hom.left) (J.comap f.hom.left)) ≫
        closedSubschemePreimageMap f I =
          closedSubschemePreimageMap f (I ⊔ J) ≫ closedSubschemeIntersectionFst Y I J := by
  rw [closedSubschemePreimageIntersectionIso_hom_fst]
  exact closedSubschemePreimageInclusion_map f le_sup_left

/-- The second projection followed by restriction agrees with restriction then projection. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageIntersectionIso_hom_snd_map (f : X ⟶ Y)
    (I J : Y.toScheme.IdealSheafData) :
    ((closedSubschemePreimageIntersectionIso f I J).hom ≫
      closedSubschemeIntersectionSnd X (I.comap f.hom.left) (J.comap f.hom.left)) ≫
        closedSubschemePreimageMap f J =
          closedSubschemePreimageMap f (I ⊔ J) ≫ closedSubschemeIntersectionSnd Y I J := by
  rw [closedSubschemePreimageIntersectionIso_hom_snd]
  exact closedSubschemePreimageInclusion_map f le_sup_right

end Variety

end

end LeanVarieties
