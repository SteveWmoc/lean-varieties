import LeanVarieties.ClosedSubschemePullback

/-!
# Symmetry and absorption of closed-subscheme intersections

The canonical symmetry swaps the projections. If `J ≤ I`, the intersection
defined by `I ⊔ J` recovers the subscheme defined by `I` via its first projection.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Swap the factors of a scheme-theoretic intersection. -/
def closedSubschemeIntersectionSwap (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I J ⟶ closedSubschemeIntersection Y J I :=
  closedSubschemeIntersectionLift Y J I
    (closedSubschemeIntersectionSnd Y I J) (closedSubschemeIntersectionFst Y I J) (by simp)

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionSwap_fst (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersectionSwap Y I J ≫ closedSubschemeIntersectionFst Y J I =
      closedSubschemeIntersectionSnd Y I J :=
  closedSubschemeIntersectionLift_fst Y J I _ _ _

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionSwap_snd (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersectionSwap Y I J ≫ closedSubschemeIntersectionSnd Y J I =
      closedSubschemeIntersectionFst Y I J :=
  closedSubschemeIntersectionLift_snd Y J I _ _ _

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionSwap_swap (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersectionSwap Y I J ≫ closedSubschemeIntersectionSwap Y J I =
      𝟙 (closedSubschemeIntersection Y I J) := by
  apply (closedSubschemeIntersection_isPullback Y I J).hom_ext <;> simp

/-- Symmetry of intersections, with the inverse given by swapping again. -/
def closedSubschemeIntersectionSymmetry (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I J ≅ closedSubschemeIntersection Y J I where
  hom := closedSubschemeIntersectionSwap Y I J
  inv := closedSubschemeIntersectionSwap Y J I
  hom_inv_id := closedSubschemeIntersectionSwap_swap Y I J
  inv_hom_id := closedSubschemeIntersectionSwap_swap Y J I

/-- If `J ≤ I`, the first subscheme is contained in the second, so its
intersection with the second is canonically itself. -/
def closedSubschemeIntersectionAbsorption (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) (h : J ≤ I) :
    closedSubschemeIntersection Y I J ≅ closedSubscheme Y I where
  hom := closedSubschemeIntersectionFst Y I J
  inv := closedSubschemeInclusion Y (sup_le le_rfl h)
  hom_inv_id := by
    apply closedSubscheme_hom_ext Y (I ⊔ J)
    simp
  inv_hom_id := by
    apply closedSubscheme_hom_ext Y I
    simp

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionAbsorption_inv_fst (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) (h : J ≤ I) :
    (closedSubschemeIntersectionAbsorption Y I J h).inv ≫
      closedSubschemeIntersectionFst Y I J = 𝟙 (closedSubscheme Y I) :=
  (closedSubschemeIntersectionAbsorption Y I J h).inv_hom_id

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionAbsorption_inv_snd (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) (h : J ≤ I) :
    (closedSubschemeIntersectionAbsorption Y I J h).inv ≫
      closedSubschemeIntersectionSnd Y I J = closedSubschemeInclusion Y h := by
  apply closedSubscheme_hom_ext Y J
  change (closedSubschemeInclusion Y (sup_le le_rfl h) ≫
    closedSubschemeIntersectionSnd Y I J) ≫ closedSubschemeι Y J = _
  rw [Category.assoc, closedSubschemeIntersectionSnd_ι,
    closedSubschemeInclusion_ι, closedSubschemeInclusion_ι]

/-- Intersecting a closed subscheme with itself recovers that subscheme. -/
def closedSubschemeIntersectionSelfIso (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I I ≅ closedSubscheme Y I :=
  closedSubschemeIntersectionAbsorption Y I I le_rfl

end Variety

end

end LeanVarieties
