import LeanVarieties.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Projective varieties

A variety over `k` is projective if it admits a closed immersion over
`Spec k` into some projective space. The embedding is existential data in
a proposition, so projectivity is a property of the variety.

Closed immersions into projective varieties preserve projectivity, and
projective varieties are proper. This file also packages projectivity and
smooth projectivity as full subcategories.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- A variety is projective if it admits a closed immersion into projective space
that commutes with the structural morphisms to the base field. -/
@[mk_iff]
class IsProjective (X : Variety k) : Prop where
  /-- A closed immersion over the base into some projective space. -/
  exists_closedImmersion :
    ∃ (n : ℕ) (i : X.toScheme ⟶ projectiveScheme k n),
      IsClosedImmersion i ∧ i ≫ projectiveStructureMap k n = X.structureMap

/-- A closed subvariety of a projective variety is projective. -/
lemma IsProjective.of_closedImmersion {X Y : Variety k} [Y.IsProjective]
    (i : X.toScheme ⟶ Y.toScheme) [IsClosedImmersion i]
    (hi : i ≫ Y.structureMap = X.structureMap) : X.IsProjective := by
  obtain ⟨n, j, hj, hcomm⟩ := IsProjective.exists_closedImmersion (X := Y)
  let : IsClosedImmersion j := hj
  refine ⟨n, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hcomm, hi]

/-- Projective varieties are proper over their base field. -/
instance (priority := 100) IsProjective.isProper (X : Variety k) [X.IsProjective] :
    X.IsProper := by
  obtain ⟨n, i, hi, hcomm⟩ := IsProjective.exists_closedImmersion (X := X)
  let : IsClosedImmersion i := hi
  change AlgebraicGeometry.IsProper X.structureMap
  rw [← hcomm]
  infer_instance

/-- Projective space is projective via its identity closed immersion. -/
instance projectiveSpace_isProjective (n : ℕ) :
    (projectiveSpace (k := k) n).IsProjective := by
  refine ⟨n, 𝟙 (projectiveScheme k n), inferInstance, ?_⟩
  exact Category.id_comp _

/-- Projectivity as an object property on varieties. -/
def projectiveProperty (k : Type u) [Field k] : ObjectProperty (Variety k) :=
  fun X => X.IsProjective

/-- Smoothness and projectivity as a joint object property on varieties. -/
def smoothProjectiveProperty (k : Type u) [Field k] : ObjectProperty (Variety k) :=
  fun X => X.IsSmooth ∧ X.IsProjective

end Variety

/-- The full subcategory of projective varieties over `k`. -/
abbrev ProjectiveVariety (k : Type u) [Field k] :=
  (Variety.projectiveProperty k).FullSubcategory

/-- The full subcategory of smooth projective varieties over `k`. -/
abbrev SmoothProjectiveVariety (k : Type u) [Field k] :=
  (Variety.smoothProjectiveProperty k).FullSubcategory

namespace ProjectiveVariety

variable {k : Type u} [Field k]

instance isProjective (X : ProjectiveVariety k) : X.obj.IsProjective :=
  X.property

end ProjectiveVariety

namespace SmoothProjectiveVariety

variable {k : Type u} [Field k]

instance isSmooth (X : SmoothProjectiveVariety k) : X.obj.IsSmooth :=
  X.property.1

instance isProjective (X : SmoothProjectiveVariety k) : X.obj.IsProjective :=
  X.property.2

end SmoothProjectiveVariety

/-- Projective complex algebraic varieties. -/
abbrev ProjectiveComplexVariety := ProjectiveVariety ℂ

/-- Smooth projective complex algebraic varieties. -/
abbrev SmoothProjectiveComplexVariety := SmoothProjectiveVariety ℂ

end

end LeanVarieties
