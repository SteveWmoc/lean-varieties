import LeanVarieties.Projective
import LeanVarieties.Dimension

/-!
# Closed subvarieties of projective varieties

A morphism in `Variety k` already commutes with the structural morphisms to
`Spec k`. Hence a closed immersion of varieties into a projective variety
makes its source projective without requiring a separate base-compatibility
proof.

If the source is also known to be smooth, it can be packaged immediately as a
smooth projective variety.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- A closed immersion of varieties into a projective variety has projective source.

Unlike `IsProjective.of_closedImmersion`, the compatibility with the
structural morphisms is automatic because `f` is a morphism in `Variety k`.
-/
lemma IsProjective.of_closedImmersion_hom {X Y : Variety k} [Y.IsProjective]
    (f : X ⟶ Y) [IsClosedImmersion f.hom.left] : X.IsProjective :=
  IsProjective.of_closedImmersion f.hom.left (Over.w f.hom)

end Variety

namespace ProjectiveVariety

variable {k : Type u} [Field k]

/-- Package the source of a closed immersion into a projective variety as a
projective variety. -/
def ofClosedImmersion {X : Variety k} (Y : ProjectiveVariety k) (f : X ⟶ Y.obj)
    [IsClosedImmersion f.hom.left] : ProjectiveVariety k :=
  ⟨X, Variety.IsProjective.of_closedImmersion_hom f⟩

@[simp]
lemma ofClosedImmersion_obj {X : Variety k} (Y : ProjectiveVariety k) (f : X ⟶ Y.obj)
    [IsClosedImmersion f.hom.left] :
    (ofClosedImmersion Y f).obj = X := rfl

end ProjectiveVariety

namespace SmoothProjectiveVariety

variable {k : Type u} [Field k]

/-- Package a smooth variety admitting a closed immersion into a projective
variety as a smooth projective variety. -/
def ofClosedImmersion {X : Variety k} [X.IsSmooth] (Y : ProjectiveVariety k)
    (f : X ⟶ Y.obj) [IsClosedImmersion f.hom.left] :
    SmoothProjectiveVariety k :=
  ⟨X, ⟨inferInstance, Variety.IsProjective.of_closedImmersion_hom f⟩⟩

@[simp]
lemma ofClosedImmersion_obj {X : Variety k} [X.IsSmooth] (Y : ProjectiveVariety k)
    (f : X ⟶ Y.obj) [IsClosedImmersion f.hom.left] :
    (ofClosedImmersion Y f).obj = X := rfl

end SmoothProjectiveVariety

namespace SmoothProjectiveVarietyOfDimension

variable {k : Type u} [Field k] {n : ℕ}

/-- Package a smooth variety of dimension `n` admitting a closed immersion
into a projective variety as a smooth projective variety of dimension `n`.
The dimension witness is required for the source, independently of the target. -/
def ofClosedImmersion {X : Variety k} [X.IsSmoothOfDimension n]
    (Y : ProjectiveVariety k) (f : X ⟶ Y.obj) [IsClosedImmersion f.hom.left] :
    SmoothProjectiveVarietyOfDimension k n :=
  ⟨X, ⟨inferInstance, Variety.IsProjective.of_closedImmersion_hom f⟩⟩

@[simp]
lemma ofClosedImmersion_obj {X : Variety k} [X.IsSmoothOfDimension n]
    (Y : ProjectiveVariety k) (f : X ⟶ Y.obj) [IsClosedImmersion f.hom.left] :
    (ofClosedImmersion (n := n) Y f).obj = X := rfl

/-- Package a smooth `n`-dimensional variety embedded as a closed subvariety
of projective `m`-space. The ambient dimension `m` can differ from `n`. -/
def ofProjectiveSpace {X : Variety k} [X.IsSmoothOfDimension n] (m : ℕ)
    (f : X ⟶ Variety.projectiveSpace (k := k) m) [IsClosedImmersion f.hom.left] :
    SmoothProjectiveVarietyOfDimension k n :=
  ofClosedImmersion
    ⟨Variety.projectiveSpace (k := k) m, Variety.projectiveSpace_isProjective m⟩ f

@[simp]
lemma ofProjectiveSpace_obj {X : Variety k} [X.IsSmoothOfDimension n] (m : ℕ)
    (f : X ⟶ Variety.projectiveSpace (k := k) m) [IsClosedImmersion f.hom.left] :
    (ofProjectiveSpace (n := n) m f).obj = X := rfl

end SmoothProjectiveVarietyOfDimension

end

end LeanVarieties
