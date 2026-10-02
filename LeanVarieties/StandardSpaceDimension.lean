import LeanVarieties.Dimension
import LeanVarieties.ProjectiveChartCoordinates

/-!
# Standard spaces of fixed dimension

Affine and projective `n`-space are smooth of relative dimension `n`.
The affine witness is supplied by mathlib; the projective witness follows
from the standard affine charts and locality on the source.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

/-- Affine `n`-space is smooth of dimension `n`. -/
instance affineSpace_isSmoothOfDimension (n : ℕ) :
    (affineSpace (k := k) n).IsSmoothOfDimension n := by
  change SmoothOfRelativeDimension n ((affineScheme k n) ↘ baseScheme k)
  infer_instance

set_option linter.style.haveILetI false in
/-- Projective `n`-space is smooth of dimension `n`. -/
instance projectiveSpace_isSmoothOfDimension (n : ℕ) :
    (projectiveSpace (k := k) n).IsSmoothOfDimension n := by
  let : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} n) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @SmoothOfRelativeDimension.{u} n)]
    exact affineLocally_respectsIso _
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  let 𝒰 := (projectiveScheme k n).openCoverOfIsOpenCover
    (ProjectiveSpace.coordinateOpen k n)
    (ProjectiveSpace.iSup_coordinateOpen_eq_top k n)
  haveI : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by
    dsimp [𝒰, Scheme.openCoverOfIsOpenCover] at i ⊢
    exact ProjectiveSpace.isAffineOpen_coordinateOpen k n i
  change SmoothOfRelativeDimension n (projectiveStructureMap k n)
  rw [HasRingHomProperty.iff_of_source_openCover (P := @SmoothOfRelativeDimension.{u} n) 𝒰]
  intro i
  dsimp [𝒰, Scheme.openCoverOfIsOpenCover] at i
  have hLocal :
      SmoothOfRelativeDimension n
        ((ProjectiveSpace.coordinateOpen k n i).ι ≫ projectiveStructureMap k n) := by
    rw [← ProjectiveSpace.coordinateOpenIsoAffineSpace_hom_structureMap,
      MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{u} n)
        (ProjectiveSpace.coordinateOpenIsoAffineSpace k n i).hom]
    exact affineSpace_isSmoothOfDimension n
  have hLocal' : SmoothOfRelativeDimension n (𝒰.f i ≫ projectiveStructureMap k n) := by
    simpa [𝒰, Scheme.openCoverOfIsOpenCover] using hLocal
  haveI : IsAffine (𝒰.X i) := by
    dsimp [𝒰, Scheme.openCoverOfIsOpenCover]
    exact ProjectiveSpace.isAffineOpen_coordinateOpen k n i
  exact HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension.{u} n) _ hLocal'

end Variety

namespace SmoothVarietyOfDimension

variable {k : Type u} [Field k]

/-- Affine `n`-space as a smooth variety of dimension `n`. -/
def affineSpace (n : ℕ) : SmoothVarietyOfDimension k n :=
  ⟨Variety.affineSpace (k := k) n, Variety.affineSpace_isSmoothOfDimension n⟩

@[simp]
lemma affineSpace_obj (n : ℕ) :
    (affineSpace (k := k) n).obj = Variety.affineSpace (k := k) n := rfl

/-- Projective `n`-space as a smooth variety of dimension `n`. -/
def projectiveSpace (n : ℕ) : SmoothVarietyOfDimension k n :=
  ⟨Variety.projectiveSpace (k := k) n, Variety.projectiveSpace_isSmoothOfDimension n⟩

@[simp]
lemma projectiveSpace_obj (n : ℕ) :
    (projectiveSpace (k := k) n).obj = Variety.projectiveSpace (k := k) n := rfl

end SmoothVarietyOfDimension

namespace SmoothProjectiveVarietyOfDimension

variable {k : Type u} [Field k]

/-- Projective `n`-space as a smooth projective variety of dimension `n`. -/
def projectiveSpace (n : ℕ) : SmoothProjectiveVarietyOfDimension k n :=
  ⟨Variety.projectiveSpace (k := k) n,
    ⟨Variety.projectiveSpace_isSmoothOfDimension n, Variety.projectiveSpace_isProjective n⟩⟩

@[simp]
lemma projectiveSpace_obj (n : ℕ) :
    (projectiveSpace (k := k) n).obj = Variety.projectiveSpace (k := k) n := rfl

end SmoothProjectiveVarietyOfDimension

end

end LeanVarieties
