import LeanVarieties.ClosedSubschemePreimagePullback

/-!
# Identity and composition of inverse images

Equal ideal-sheaf data gives a canonical isomorphism over the ambient variety.
This identifies inverse images along identities and composites, with compatibility
for the inclusions and restricted maps.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Equal ideal-sheaf data defines canonically isomorphic closed subschemes. -/
def closedSubschemeCongr (X : Variety k) {I J : X.toScheme.IdealSheafData} (h : I = J) :
    closedSubscheme X I ≅ closedSubscheme X J :=
  eqToIso (congrArg (closedSubscheme X) h)

@[reassoc (attr := simp)]
lemma closedSubschemeCongr_hom_ι (X : Variety k)
    {I J : X.toScheme.IdealSheafData} (h : I = J) :
    (closedSubschemeCongr X h).hom ≫ closedSubschemeι X J = closedSubschemeι X I := by
  subst J
  simp [closedSubschemeCongr]

@[reassoc (attr := simp)]
lemma closedSubschemeCongr_inv_ι (X : Variety k)
    {I J : X.toScheme.IdealSheafData} (h : I = J) :
    (closedSubschemeCongr X h).inv ≫ closedSubschemeι X I = closedSubschemeι X J := by
  subst J
  simp [closedSubschemeCongr]

/-- Pulling back along an identity recovers the original closed subscheme. -/
def closedSubschemePreimageIdIso (X : Variety k) (I : X.toScheme.IdealSheafData) :
    closedSubschemePreimage (𝟙 X) I ≅ closedSubscheme X I :=
  closedSubschemeCongr X (by
    change I.comap (𝟙 X.toScheme) = I
    exact I.comap_id)

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIdIso_hom_ι (X : Variety k)
    (I : X.toScheme.IdealSheafData) :
    (closedSubschemePreimageIdIso X I).hom ≫ closedSubschemeι X I =
      closedSubschemePreimageι (𝟙 X) I :=
  closedSubschemeCongr_hom_ι X _

@[reassoc (attr := simp)]
lemma closedSubschemePreimageIdIso_inv_ι (X : Variety k)
    (I : X.toScheme.IdealSheafData) :
    (closedSubschemePreimageIdIso X I).inv ≫ closedSubschemePreimageι (𝟙 X) I =
      closedSubschemeι X I :=
  closedSubschemeCongr_inv_ι X _

/-- The identity comparison is the canonical restricted map. -/
lemma closedSubschemePreimageIdIso_hom (X : Variety k)
    (I : X.toScheme.IdealSheafData) :
    (closedSubschemePreimageIdIso X I).hom = closedSubschemePreimageMap (𝟙 X) I := by
  apply closedSubscheme_hom_ext X I
  rw [closedSubschemePreimageIdIso_hom_ι, closedSubschemePreimageMap_ι, Category.comp_id]

variable {X Y Z : Variety k}

/-- Inverse image along a composite agrees with successive inverse images. -/
def closedSubschemePreimageCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Z.toScheme.IdealSheafData) :
    closedSubschemePreimage (f ≫ g) I ≅ closedSubschemePreimage f (I.comap g.hom.left) :=
  closedSubschemeCongr X (by
    change I.comap (f.hom.left ≫ g.hom.left) = (I.comap g.hom.left).comap f.hom.left
    exact I.comap_comp f.hom.left g.hom.left)

@[reassoc (attr := simp)]
lemma closedSubschemePreimageCompIso_hom_ι (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Z.toScheme.IdealSheafData) :
    (closedSubschemePreimageCompIso f g I).hom ≫
      closedSubschemePreimageι f (I.comap g.hom.left) =
        closedSubschemePreimageι (f ≫ g) I :=
  closedSubschemeCongr_hom_ι X _

@[reassoc (attr := simp)]
lemma closedSubschemePreimageCompIso_inv_ι (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Z.toScheme.IdealSheafData) :
    (closedSubschemePreimageCompIso f g I).inv ≫ closedSubschemePreimageι (f ≫ g) I =
      closedSubschemePreimageι f (I.comap g.hom.left) :=
  closedSubschemeCongr_inv_ι X _

/-- The composition comparison respects the restricted maps to the original subscheme. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageCompIso_hom_map (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Z.toScheme.IdealSheafData) :
    (closedSubschemePreimageCompIso f g I).hom ≫
      closedSubschemePreimageMap f (I.comap g.hom.left) ≫ closedSubschemePreimageMap g I =
        closedSubschemePreimageMap (f ≫ g) I := by
  apply closedSubscheme_hom_ext Z I
  simp only [Category.assoc, closedSubschemePreimageMap_ι]
  change (closedSubschemePreimageCompIso f g I).hom ≫
    closedSubschemePreimageMap f (I.comap g.hom.left) ≫
      closedSubschemeι Y (I.comap g.hom.left) ≫ g = _
  rw [closedSubschemePreimageMap_ι_assoc, closedSubschemePreimageCompIso_hom_ι_assoc]

/-- The inverse comparison also respects the maps to the original subscheme. -/
@[reassoc (attr := simp)]
lemma closedSubschemePreimageCompIso_inv_map (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : Z.toScheme.IdealSheafData) :
    (closedSubschemePreimageCompIso f g I).inv ≫ closedSubschemePreimageMap (f ≫ g) I =
      closedSubschemePreimageMap f (I.comap g.hom.left) ≫ closedSubschemePreimageMap g I := by
  rw [← closedSubschemePreimageCompIso_hom_map f g I, Iso.inv_hom_id_assoc]

end Variety

end

end LeanVarieties
