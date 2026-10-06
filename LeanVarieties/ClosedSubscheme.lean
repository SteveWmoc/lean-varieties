import LeanVarieties.ClosedSubvariety

/-!
# Closed subschemes as varieties

The source of a closed immersion into a variety is again a variety over the
same field. This file constructs that variety and its inclusion morphism,
then specializes the construction to the subscheme defined by ideal sheaf data.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Regard the source of a closed immersion into a variety as a variety.
Its structural map is the composite through the ambient variety. -/
def ofClosedImmersion (Y : Variety k) {X : Scheme.{u}} (i : X ⟶ Y.toScheme)
    [IsClosedImmersion i] : Variety k :=
  ofScheme X (i ≫ Y.structureMap)

@[simp]
lemma ofClosedImmersion_toScheme (Y : Variety k) {X : Scheme.{u}}
    (i : X ⟶ Y.toScheme) [IsClosedImmersion i] :
    (ofClosedImmersion Y i).toScheme = X := rfl

@[simp]
lemma ofClosedImmersion_structureMap (Y : Variety k) {X : Scheme.{u}}
    (i : X ⟶ Y.toScheme) [IsClosedImmersion i] :
    (ofClosedImmersion Y i).structureMap = i ≫ Y.structureMap := rfl

/-- The original closed immersion, now as a morphism of varieties over `k`. -/
def closedImmersionι (Y : Variety k) {X : Scheme.{u}} (i : X ⟶ Y.toScheme)
    [IsClosedImmersion i] : ofClosedImmersion Y i ⟶ Y :=
  ObjectProperty.homMk (Over.homMk i rfl)

@[simp]
lemma closedImmersionι_hom_left (Y : Variety k) {X : Scheme.{u}}
    (i : X ⟶ Y.toScheme) [IsClosedImmersion i] :
    (closedImmersionι Y i).hom.left = i := rfl

instance closedImmersionι_isClosedImmersion (Y : Variety k) {X : Scheme.{u}}
    (i : X ⟶ Y.toScheme) [IsClosedImmersion i] :
    IsClosedImmersion (closedImmersionι Y i).hom.left := by
  change IsClosedImmersion i
  infer_instance

/-- A closed subscheme of a projective variety is projective. -/
instance ofClosedImmersion_isProjective (Y : Variety k) [Y.IsProjective]
    {X : Scheme.{u}} (i : X ⟶ Y.toScheme) [IsClosedImmersion i] :
    (ofClosedImmersion Y i).IsProjective :=
  IsProjective.of_closedImmersion_hom (closedImmersionι Y i)

/-- The closed subvariety defined by ideal sheaf data on an ambient variety.
No reducedness or smoothness hypothesis is imposed. -/
def closedSubscheme (Y : Variety k) (I : Y.toScheme.IdealSheafData) : Variety k :=
  ofClosedImmersion Y I.subschemeι

@[simp]
lemma closedSubscheme_toScheme (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    (closedSubscheme Y I).toScheme = I.subscheme := rfl

@[simp]
lemma closedSubscheme_structureMap (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    (closedSubscheme Y I).structureMap = I.subschemeι ≫ Y.structureMap := rfl

/-- The inclusion of the subscheme defined by ideal sheaf data, over `k`. -/
def closedSubschemeι (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    closedSubscheme Y I ⟶ Y :=
  closedImmersionι Y I.subschemeι

@[simp]
lemma closedSubschemeι_hom_left (Y : Variety k) (I : Y.toScheme.IdealSheafData) :
    (closedSubschemeι Y I).hom.left = I.subschemeι := rfl

instance closedSubschemeι_isClosedImmersion (Y : Variety k)
    (I : Y.toScheme.IdealSheafData) :
    IsClosedImmersion (closedSubschemeι Y I).hom.left := by
  change IsClosedImmersion I.subschemeι
  infer_instance

instance closedSubscheme_isProjective (Y : Variety k) [Y.IsProjective]
    (I : Y.toScheme.IdealSheafData) : (closedSubscheme Y I).IsProjective := by
  change (ofClosedImmersion Y I.subschemeι).IsProjective
  infer_instance

end Variety

end

end LeanVarieties
