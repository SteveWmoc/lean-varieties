import LeanVarieties.ClosedSubscheme

/-!
# Inclusions between closed subschemes

An inclusion of ideal sheaves `I ≤ J` induces a closed immersion from the
subscheme defined by `J` to the subscheme defined by `I`. These maps are
morphisms of varieties over the base field and form a contravariant functor.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Larger ideals define smaller closed subschemes, with a canonical inclusion
as varieties over the same field. -/
def closedSubschemeInclusion (Y : Variety k) {I J : Y.toScheme.IdealSheafData}
    (h : I ≤ J) : closedSubscheme Y J ⟶ closedSubscheme Y I :=
  ObjectProperty.homMk (Over.homMk (Scheme.IdealSheafData.inclusion h) (by
    change Scheme.IdealSheafData.inclusion h ≫ (I.subschemeι ≫ Y.structureMap) =
      J.subschemeι ≫ Y.structureMap
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]))

@[simp]
lemma closedSubschemeInclusion_hom_left (Y : Variety k)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    (closedSubschemeInclusion Y h).hom.left = Scheme.IdealSheafData.inclusion h := rfl

instance closedSubschemeInclusion_isClosedImmersion (Y : Variety k)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (closedSubschemeInclusion Y h).hom.left := by
  change IsClosedImmersion (Scheme.IdealSheafData.inclusion h)
  infer_instance

@[reassoc (attr := simp)]
lemma closedSubschemeInclusion_ι (Y : Variety k)
    {I J : Y.toScheme.IdealSheafData} (h : I ≤ J) :
    closedSubschemeInclusion Y h ≫ closedSubschemeι Y I = closedSubschemeι Y J := by
  apply (forget k).map_injective
  change Scheme.IdealSheafData.inclusion h ≫ I.subschemeι = J.subschemeι
  exact Scheme.IdealSheafData.inclusion_subschemeι h

@[simp]
lemma closedSubschemeInclusion_id (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    closedSubschemeInclusion Y (le_refl I) = 𝟙 (closedSubscheme Y I) := by
  apply (forget k).map_injective
  change Scheme.IdealSheafData.inclusion (le_refl I) = 𝟙 I.subscheme
  exact Scheme.IdealSheafData.inclusion_id I

@[reassoc (attr := simp)]
lemma closedSubschemeInclusion_comp (Y : Variety k)
    {I J K : Y.toScheme.IdealSheafData} (hIJ : I ≤ J) (hJK : J ≤ K) :
    closedSubschemeInclusion Y hJK ≫ closedSubschemeInclusion Y hIJ =
      closedSubschemeInclusion Y (hIJ.trans hJK) := by
  apply (forget k).map_injective
  change Scheme.IdealSheafData.inclusion hJK ≫ Scheme.IdealSheafData.inclusion hIJ =
    Scheme.IdealSheafData.inclusion (hIJ.trans hJK)
  exact Scheme.IdealSheafData.inclusion_comp hIJ hJK

/-- Ideal sheaf data defines closed subvarieties contravariantly. -/
def closedSubschemeFunctor (Y : Variety k) :
    (Y.toScheme.IdealSheafData)ᵒᵖ ⥤ Variety k where
  obj I := closedSubscheme Y I.unop
  map f := closedSubschemeInclusion Y f.unop.le
  map_id I := closedSubschemeInclusion_id Y I.unop
  map_comp f g := (closedSubschemeInclusion_comp Y g.unop.le f.unop.le).symm

end Variety

end

end LeanVarieties
