import LeanVarieties.ClosedSubschemePreimage
import LeanVarieties.ClosedSubschemeIntersection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Inverse images as pullbacks of varieties

Compatible maps lift uniquely to the scheme-theoretic inverse image. The
resulting square is a categorical pullback in `Variety k`.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k] {X Y : Variety k}

private lemma schemePreimageLift_fst (f : X.toScheme ⟶ Y.toScheme)
    (I : Y.toScheme.IdealSheafData) {T : Scheme.{u}}
    (a : T ⟶ X.toScheme) (b : T ⟶ I.subscheme) (w : a ≫ f = b ≫ I.subschemeι) :
    (pullback.lift a b w ≫ (I.comapIso f).inv) ≫ (I.comap f).subschemeι = a := by
  rw [Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι, pullback.lift_fst]

/-- Lift compatible maps to the scheme-theoretic inverse image, over the base field. -/
def closedSubschemePreimageLift (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (a : T ⟶ X) (b : T ⟶ closedSubscheme Y I)
    (w : a ≫ f = b ≫ closedSubschemeι Y I) : T ⟶ closedSubschemePreimage f I :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift (f := f.hom.left) (g := I.subschemeι) a.hom.left
      (show T.toScheme ⟶ I.subscheme from b.hom.left) ((forget k).congr_map w) ≫
      (I.comapIso f.hom.left).inv) (by
      change (pullback.lift (f := f.hom.left) (g := I.subschemeι) a.hom.left
        (show T.toScheme ⟶ I.subscheme from b.hom.left) _ ≫ (I.comapIso f.hom.left).inv) ≫
        ((I.comap f.hom.left).subschemeι ≫ X.structureMap) = T.structureMap
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ X.structureMap)
          (schemePreimageLift_fst f.hom.left I a.hom.left b.hom.left
            ((forget k).congr_map w))).trans (Over.w a.hom))))

@[reassoc (attr := simp)]
lemma closedSubschemePreimageLift_ι (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (a : T ⟶ X) (b : T ⟶ closedSubscheme Y I)
    (w : a ≫ f = b ≫ closedSubschemeι Y I) :
    closedSubschemePreimageLift f I a b w ≫ closedSubschemePreimageι f I = a := by
  apply (forget k).map_injective
  change (pullback.lift (f := f.hom.left) (g := I.subschemeι) a.hom.left
        (show T.toScheme ⟶ I.subscheme from b.hom.left) _ ≫ (I.comapIso f.hom.left).inv) ≫
    (I.comap f.hom.left).subschemeι = a.hom.left
  exact schemePreimageLift_fst f.hom.left I a.hom.left b.hom.left ((forget k).congr_map w)

@[reassoc (attr := simp)]
lemma closedSubschemePreimageLift_map (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (a : T ⟶ X) (b : T ⟶ closedSubscheme Y I)
    (w : a ≫ f = b ≫ closedSubschemeι Y I) :
    closedSubschemePreimageLift f I a b w ≫ closedSubschemePreimageMap f I = b := by
  apply closedSubscheme_hom_ext Y I
  rw [Category.assoc, closedSubschemePreimageMap_ι, ← Category.assoc,
    closedSubschemePreimageLift_ι]
  exact w

/-- Maps into the inverse image are determined by their composite into `X`. -/
lemma closedSubschemePreimage_hom_ext (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} {a b : T ⟶ closedSubschemePreimage f I}
    (h : a ≫ closedSubschemePreimageι f I = b ≫ closedSubschemePreimageι f I) : a = b :=
  closedSubscheme_hom_ext X (I.comap f.hom.left) h

/-- Compatible maps lift uniquely to the inverse image. -/
lemma closedSubschemePreimage_existsUnique (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (a : T ⟶ X) (b : T ⟶ closedSubscheme Y I)
    (w : a ≫ f = b ≫ closedSubschemeι Y I) :
    ∃! l : T ⟶ closedSubschemePreimage f I,
      l ≫ closedSubschemePreimageι f I = a ∧ l ≫ closedSubschemePreimageMap f I = b := by
  refine ⟨closedSubschemePreimageLift f I a b w, ⟨by simp, by simp⟩, ?_⟩
  intro l hl
  apply closedSubschemePreimage_hom_ext f I
  rw [hl.1, closedSubschemePreimageLift_ι]

/-- The inverse-image square is a pullback in the category of varieties. -/
lemma closedSubschemePreimage_isPullback (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    IsPullback (closedSubschemePreimageι f I) (closedSubschemePreimageMap f I)
      f (closedSubschemeι Y I) := by
  refine IsPullback.mk' (closedSubschemePreimageMap_ι f I).symm ?_ ?_
  · intro T a b hι _hmap
    exact closedSubschemePreimage_hom_ext f I hι
  · intro T a b w
    exact (closedSubschemePreimage_existsUnique f I a b w).exists

/-- Pullbacks along canonical closed-subscheme inclusions exist in `Variety k`. -/
instance closedSubschemePreimage_hasPullback (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    HasPullback f (closedSubschemeι Y I) :=
  (closedSubschemePreimage_isPullback f I).hasPullback

/-- Compare the explicit inverse image with mathlib's chosen pullback. -/
def closedSubschemePreimagePullbackIso (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    closedSubschemePreimage f I ≅ pullback f (closedSubschemeι Y I) :=
  (closedSubschemePreimage_isPullback f I).isoPullback

@[reassoc (attr := simp)]
lemma closedSubschemePreimagePullbackIso_hom_fst (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimagePullbackIso f I).hom ≫ pullback.fst f (closedSubschemeι Y I) =
      closedSubschemePreimageι f I :=
  (closedSubschemePreimage_isPullback f I).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma closedSubschemePreimagePullbackIso_hom_snd (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimagePullbackIso f I).hom ≫ pullback.snd f (closedSubschemeι Y I) =
      closedSubschemePreimageMap f I :=
  (closedSubschemePreimage_isPullback f I).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma closedSubschemePreimagePullbackIso_inv_ι (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimagePullbackIso f I).inv ≫ closedSubschemePreimageι f I =
      pullback.fst f (closedSubschemeι Y I) :=
  (closedSubschemePreimage_isPullback f I).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma closedSubschemePreimagePullbackIso_inv_map (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimagePullbackIso f I).inv ≫ closedSubschemePreimageMap f I =
      pullback.snd f (closedSubschemeι Y I) :=
  (closedSubschemePreimage_isPullback f I).isoPullback_inv_snd

/-- The explicit lift agrees with the standard chosen-pullback lift under comparison. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageLift_pullbackIso_hom (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) {T : Variety k}
    (a : T ⟶ X) (b : T ⟶ closedSubscheme Y I)
    (w : a ≫ f = b ≫ closedSubschemeι Y I) :
    closedSubschemePreimageLift f I a b w ≫ (closedSubschemePreimagePullbackIso f I).hom =
      pullback.lift a b w := by
  apply pullback.hom_ext
  · rw [Category.assoc, closedSubschemePreimagePullbackIso_hom_fst,
      closedSubschemePreimageLift_ι, pullback.lift_fst]
  · rw [Category.assoc, closedSubschemePreimagePullbackIso_hom_snd,
      closedSubschemePreimageLift_map, pullback.lift_snd]

end Variety

end

end LeanVarieties
