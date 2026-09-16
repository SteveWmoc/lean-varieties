import LeanVarieties.ProjectiveChartCoordinates

/-!
# Smoothness of projective space

Projective space is covered by its standard coordinate opens, and each of
those opens is isomorphic over the base field to affine space. Since smoothness
is Zariski-local on the source, the affine-space smoothness instance therefore
implies smoothness of projective space.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Variety

variable {k : Type u} [Field k]

set_option linter.style.haveILetI false in
/-- Projective `n`-space is smooth over its base field. -/
instance projectiveSpace_isSmooth (n : ℕ) :
    (projectiveSpace (k := k) n).IsSmooth := by
  let : MorphismProperty.RespectsIso (@Smooth.{u}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth.{u})]
    exact affineLocally_respectsIso _ RingHom.Smooth.respectsIso
  let 𝒰 := (projectiveScheme k n).openCoverOfIsOpenCover
    (ProjectiveSpace.coordinateOpen k n)
    (ProjectiveSpace.iSup_coordinateOpen_eq_top k n)
  haveI : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by
    dsimp [𝒰, Scheme.openCoverOfIsOpenCover] at i ⊢
    exact ProjectiveSpace.isAffineOpen_coordinateOpen k n i
  change Smooth (projectiveStructureMap k n)
  rw [HasRingHomProperty.iff_of_source_openCover (P := @Smooth.{u}) 𝒰]
  intro i
  dsimp [𝒰, Scheme.openCoverOfIsOpenCover] at i
  have hLocal :
      Smooth ((ProjectiveSpace.coordinateOpen k n i).ι ≫ projectiveStructureMap k n) := by
    rw [← ProjectiveSpace.coordinateOpenIsoAffineSpace_hom_structureMap,
      MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{u})
        (ProjectiveSpace.coordinateOpenIsoAffineSpace k n i).hom]
    exact affineSpace_isSmooth n
  have hLocal' : Smooth (𝒰.f i ≫ projectiveStructureMap k n) := by
    simpa [𝒰, Scheme.openCoverOfIsOpenCover] using hLocal
  exact HasRingHomProperty.appTop (P := @Smooth.{u}) _ hLocal'

end Variety

end

end LeanVarieties
