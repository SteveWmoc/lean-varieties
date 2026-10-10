import LeanVarieties.ClosedSubschemeInclusions

/-!
# Scheme-theoretic intersections of closed subvarieties

The sum of two ideal sheaves defines their scheme-theoretic intersection.
The canonical projections are closed immersions, and compatible maps to the
two factors lift uniquely to the intersection over the base field.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Lift a variety morphism to a closed subscheme when its equations vanish. -/
def closedSubschemeLift (Y : Variety k) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ Y) (h : I ≤ f.hom.left.ker) :
    T ⟶ closedSubscheme Y I :=
  ObjectProperty.homMk (Over.homMk
    (IsClosedImmersion.lift I.subschemeι f.hom.left (by simpa using h)) (by
      change IsClosedImmersion.lift I.subschemeι f.hom.left _ ≫
        (I.subschemeι ≫ Y.structureMap) = T.structureMap
      rw [← Category.assoc, IsClosedImmersion.lift_fac]
      exact Over.w f.hom))

@[reassoc (attr := simp)]
lemma closedSubschemeLift_ι (Y : Variety k) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ Y) (h : I ≤ f.hom.left.ker) :
    closedSubschemeLift Y I f h ≫ closedSubschemeι Y I = f := by
  apply (forget k).map_injective
  exact IsClosedImmersion.lift_fac I.subschemeι f.hom.left _

/-- Maps into a closed subscheme are determined by their ambient composite. -/
lemma closedSubscheme_hom_ext (Y : Variety k) (I : Y.toScheme.IdealSheafData)
    {T : Variety k} {f g : T ⟶ closedSubscheme Y I}
    (h : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y I) : f = g := by
  apply (forget k).map_injective
  apply (cancel_mono I.subschemeι).1
  exact (forget k).congr_map h

/-- Combine both sets of equations, retaining the resulting scheme structure. -/
abbrev closedSubschemeIntersection (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    Variety k :=
  closedSubscheme Y (I ⊔ J)

/-- The canonical closed immersion from the intersection to the first factor. -/
def closedSubschemeIntersectionFst (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I J ⟶ closedSubscheme Y I :=
  closedSubschemeInclusion Y le_sup_left

/-- The canonical closed immersion from the intersection to the second factor. -/
def closedSubschemeIntersectionSnd (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersection Y I J ⟶ closedSubscheme Y J :=
  closedSubschemeInclusion Y le_sup_right

instance closedSubschemeIntersectionFst_isClosedImmersion (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    IsClosedImmersion (closedSubschemeIntersectionFst Y I J).hom.left := by
  change IsClosedImmersion (closedSubschemeInclusion Y (le_sup_left : I ≤ I ⊔ J)).hom.left
  infer_instance

instance closedSubschemeIntersectionSnd_isClosedImmersion (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) :
    IsClosedImmersion (closedSubschemeIntersectionSnd Y I J).hom.left := by
  change IsClosedImmersion (closedSubschemeInclusion Y (le_sup_right : J ≤ I ⊔ J)).hom.left
  infer_instance

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionFst_ι (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersectionFst Y I J ≫ closedSubschemeι Y I =
      closedSubschemeι Y (I ⊔ J) :=
  closedSubschemeInclusion_ι Y le_sup_left

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionSnd_ι (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    closedSubschemeIntersectionSnd Y I J ≫ closedSubschemeι Y J =
      closedSubschemeι Y (I ⊔ J) :=
  closedSubschemeInclusion_ι Y le_sup_right

/-- The underlying closed set is the intersection of the two supports. -/
lemma closedSubschemeIntersection_range (Y : Variety k) (I J : Y.toScheme.IdealSheafData) :
    Set.range (closedSubschemeι Y (I ⊔ J)).hom.left =
      (I.support : Set Y.toScheme) ∩ (J.support : Set Y.toScheme) := by
  change Set.range (I ⊔ J).subschemeι = _
  simpa only [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf] using
    (I ⊔ J).range_subschemeι

/-- Compatible maps to both closed subschemes factor through their intersection. -/
def closedSubschemeIntersectionLift (Y : Variety k) (I J : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    T ⟶ closedSubschemeIntersection Y I J :=
  closedSubschemeLift Y (I ⊔ J) (f ≫ closedSubschemeι Y I) (by
    change I ⊔ J ≤ (f.hom.left ≫ I.subschemeι).ker
    apply sup_le
    · simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        f.hom.left.le_ker_comp I.subschemeι
    · have hw : f.hom.left ≫ I.subschemeι = g.hom.left ≫ J.subschemeι :=
        (forget k).congr_map w
      rw [hw]
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        g.hom.left.le_ker_comp J.subschemeι)

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionLift_ι (Y : Variety k) (I J : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    closedSubschemeIntersectionLift Y I J f g w ≫ closedSubschemeι Y (I ⊔ J) =
      f ≫ closedSubschemeι Y I :=
  closedSubschemeLift_ι Y (I ⊔ J) _ _

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionLift_fst (Y : Variety k) (I J : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    closedSubschemeIntersectionLift Y I J f g w ≫ closedSubschemeIntersectionFst Y I J = f := by
  apply closedSubscheme_hom_ext Y I
  rw [Category.assoc, closedSubschemeIntersectionFst_ι, closedSubschemeIntersectionLift_ι]

@[reassoc (attr := simp)]
lemma closedSubschemeIntersectionLift_snd (Y : Variety k) (I J : Y.toScheme.IdealSheafData)
    {T : Variety k} (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    closedSubschemeIntersectionLift Y I J f g w ≫ closedSubschemeIntersectionSnd Y I J = g := by
  apply closedSubscheme_hom_ext Y J
  rw [Category.assoc, closedSubschemeIntersectionSnd_ι, closedSubschemeIntersectionLift_ι]
  exact w

/-- The intersection has the pullback universal property in the variety category. -/
lemma closedSubschemeIntersection_existsUnique (Y : Variety k)
    (I J : Y.toScheme.IdealSheafData) {T : Variety k}
    (f : T ⟶ closedSubscheme Y I) (g : T ⟶ closedSubscheme Y J)
    (w : f ≫ closedSubschemeι Y I = g ≫ closedSubschemeι Y J) :
    ∃! l : T ⟶ closedSubschemeIntersection Y I J,
      l ≫ closedSubschemeIntersectionFst Y I J = f ∧
        l ≫ closedSubschemeIntersectionSnd Y I J = g := by
  refine ⟨closedSubschemeIntersectionLift Y I J f g w,
    ⟨closedSubschemeIntersectionLift_fst Y I J f g w,
      closedSubschemeIntersectionLift_snd Y I J f g w⟩, ?_⟩
  intro l hl
  apply closedSubscheme_hom_ext Y (I ⊔ J)
  calc
    l ≫ closedSubschemeι Y (I ⊔ J) =
        (l ≫ closedSubschemeIntersectionFst Y I J) ≫ closedSubschemeι Y I := by
      rw [Category.assoc, closedSubschemeIntersectionFst_ι]
    _ = f ≫ closedSubschemeι Y I := by rw [hl.1]
    _ = closedSubschemeIntersectionLift Y I J f g w ≫ closedSubschemeι Y (I ⊔ J) :=
      (closedSubschemeIntersectionLift_ι Y I J f g w).symm

end Variety

end

end LeanVarieties
