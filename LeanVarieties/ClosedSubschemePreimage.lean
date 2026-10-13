import LeanVarieties.ClosedSubscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Inverse images of closed subschemes

Pull back ideal-sheaf data along a variety morphism and package the resulting
closed subscheme over the same base field. The canonical maps form a commuting
square; the categorical universal property is left to a subsequent module.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k] {X Y : Variety k}

/-- The scheme-theoretic inverse image of a closed subscheme along `f`. -/
abbrev closedSubschemePreimage (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) : Variety k :=
  closedSubscheme X (I.comap f.hom.left)

/-- The canonical inclusion of the inverse image into the source variety. -/
def closedSubschemePreimageι (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    closedSubschemePreimage f I ⟶ X :=
  closedSubschemeι X (I.comap f.hom.left)

@[simp]
lemma closedSubschemePreimageι_hom_left (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageι f I).hom.left = (I.comap f.hom.left).subschemeι := rfl

instance closedSubschemePreimageι_isClosedImmersion (f : X ⟶ Y)
    (I : Y.toScheme.IdealSheafData) :
    IsClosedImmersion (closedSubschemePreimageι f I).hom.left := by
  change IsClosedImmersion (I.comap f.hom.left).subschemeι
  infer_instance

/-- The inverse image is projective when its ambient source is projective. -/
instance closedSubschemePreimage_isProjective (f : X ⟶ Y) [X.IsProjective]
    (I : Y.toScheme.IdealSheafData) : (closedSubschemePreimage f I).IsProjective := by
  change (closedSubscheme X (I.comap f.hom.left)).IsProjective
  infer_instance

/-- The restriction of `f` from the inverse image to the original closed subscheme. -/
def closedSubschemePreimageMap (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    closedSubschemePreimage f I ⟶ closedSubscheme Y I :=
  ObjectProperty.homMk (Over.homMk
    (Scheme.IdealSheafData.subschemeMap (I.comap f.hom.left) I f.hom.left
      (I.le_map_comap f.hom.left)) (by
      change Scheme.IdealSheafData.subschemeMap _ _ _ _ ≫
        (I.subschemeι ≫ Y.structureMap) =
          (I.comap f.hom.left).subschemeι ≫ X.structureMap
      rw [← Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
        Category.assoc, Over.w f.hom]))

@[simp]
lemma closedSubschemePreimageMap_hom_left (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    (closedSubschemePreimageMap f I).hom.left =
      Scheme.IdealSheafData.subschemeMap (I.comap f.hom.left) I f.hom.left
        (I.le_map_comap f.hom.left) := rfl

@[reassoc (attr := simp)]
lemma closedSubschemePreimageMap_ι (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    closedSubschemePreimageMap f I ≫ closedSubschemeι Y I =
      closedSubschemePreimageι f I ≫ f := by
  apply (forget k).map_injective
  exact Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap f.hom.left) I f.hom.left
    (I.le_map_comap f.hom.left)

/-- The underlying closed set of the scheme-theoretic inverse image is the preimage
of the original ideal's support. -/
lemma closedSubschemePreimage_range (f : X ⟶ Y) (I : Y.toScheme.IdealSheafData) :
    Set.range (closedSubschemePreimageι f I).hom.left =
      f.hom.left ⁻¹' (I.support : Set Y.toScheme) := by
  change Set.range (I.comap f.hom.left).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage]

end Variety

end

end LeanVarieties
