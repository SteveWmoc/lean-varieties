import LeanVarieties.ClosedSubschemeIntersection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Closed-subscheme intersections as categorical pullbacks

The explicit intersection is a pullback in `Variety k`. This file connects
its universal property to mathlib's chosen pullback and standard lift API.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- The intersection square is a pullback in the category of varieties over `k`. -/
lemma closedSubschemeIntersection_isPullback (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    IsPullback (closedSubschemeIntersectionFst Y I J)
      (closedSubschemeIntersectionSnd Y I J) (closedSubschemeι Y I) (closedSubschemeι Y J) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [closedSubschemeIntersectionFst_ι, closedSubschemeIntersectionSnd_ι]
  · intro T f g hfst _hsnd
    apply closedSubscheme_hom_ext Y (I ⊔ J)
    simpa only [Category.assoc, closedSubschemeIntersectionFst_ι] using
      congrArg (fun h => h ≫ closedSubschemeι Y I) hfst
  · intro T f g w
    exact (closedSubschemeIntersection_existsUnique Y I J f g w).exists

/-- Pullbacks of two canonical closed-subscheme inclusions exist. -/
instance closedSubschemeι_hasPullback (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    HasPullback (closedSubschemeι Y I) (closedSubschemeι Y J) :=
  (closedSubschemeIntersection_isPullback Y I J).hasPullback

/-- Identify the explicit ideal-sum intersection with mathlib's chosen pullback. -/
def closedSubschemeIntersectionPullbackIso (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I J ≅ pullback (closedSubschemeι Y I) (closedSubschemeι Y J) :=
  (closedSubschemeIntersection_isPullback Y I J).isoPullback

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionPullbackIso_hom_fst (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemeIntersectionPullbackIso Y I J).hom ≫
      pullback.fst (closedSubschemeι Y I) (closedSubschemeι Y J) =
        closedSubschemeIntersectionFst Y I J :=
  (closedSubschemeIntersection_isPullback Y I J).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionPullbackIso_hom_snd (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemeIntersectionPullbackIso Y I J).hom ≫
      pullback.snd (closedSubschemeι Y I) (closedSubschemeι Y J) =
        closedSubschemeIntersectionSnd Y I J :=
  (closedSubschemeIntersection_isPullback Y I J).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionPullbackIso_inv_fst (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemeIntersectionPullbackIso Y I J).inv ≫
      closedSubschemeIntersectionFst Y I J =
        pullback.fst (closedSubschemeι Y I) (closedSubschemeι Y J) :=
  (closedSubschemeIntersection_isPullback Y I J).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionPullbackIso_inv_snd (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    (closedSubschemeIntersectionPullbackIso Y I J).inv ≫
      closedSubschemeIntersectionSnd Y I J =
        pullback.snd (closedSubschemeι Y I) (closedSubschemeι Y J) :=
  (closedSubschemeIntersection_isPullback Y I J).isoPullback_inv_snd

/-- The square witness's standard lift agrees with the explicit intersection lift. -/
@[simp]
lemma closedSubschemeIntersection_isPullback_lift (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) {T : Variety k}
    (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    (closedSubschemeIntersection_isPullback Y I J).lift f g w =
      closedSubschemeIntersectionLift Y I J f g w := by
  apply (closedSubschemeIntersection_isPullback Y I J).hom_ext
  · rw [IsPullback.lift_fst, closedSubschemeIntersectionLift_fst]
  · rw [IsPullback.lift_snd, closedSubschemeIntersectionLift_snd]

/-- The explicit lift becomes the chosen pullback lift under the comparison isomorphism. -/
@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionLift_pullbackIso_hom (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) {T : Variety k}
    (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    closedSubschemeIntersectionLift Y I J f g w ≫
      (closedSubschemeIntersectionPullbackIso Y I J).hom = pullback.lift f g w := by
  apply pullback.hom_ext
  · rw [Category.assoc, closedSubschemeIntersectionPullbackIso_hom_fst,
      closedSubschemeIntersectionLift_fst, pullback.lift_fst]
  · rw [Category.assoc, closedSubschemeIntersectionPullbackIso_hom_snd,
      closedSubschemeIntersectionLift_snd, pullback.lift_snd]

end Variety

end

end LeanVarieties
