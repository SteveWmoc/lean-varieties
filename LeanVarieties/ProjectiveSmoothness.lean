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

/-- Projective `n`-space is smooth over its base field. -/
instance projectiveSpace_isSmooth (n : ℕ) :
    (projectiveSpace (k := k) n).IsSmooth := by
  let : MorphismProperty.RespectsIso (@Smooth.{u}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth.{u})]
    exact affineLocally_respectsIso _ RingHom.Smooth.respectsIso
  haveI : ∀ i, IsAffine ((ProjectiveSpace.coordinateAffineOpenCover k n).openCover.X i) :=
    fun i => inferInstance
  change Smooth (projectiveStructureMap k n)
  rw [HasRingHomProperty.iff_of_source_openCover
    (P := @Smooth.{u}) (ProjectiveSpace.coordinateAffineOpenCover k n).openCover]
  intro i
  have hChart : Smooth (ProjectiveSpace.chartStructureMap k n i) := by
    rw [← ProjectiveSpace.chartAffineSpaceIso_hom_structureMap,
      MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{u})
        (ProjectiveSpace.chartAffineSpaceIso k n i).hom]
    exact affineSpace_isSmooth n
  have hLocal :
      Smooth ((ProjectiveSpace.coordinateAffineOpenCover k n).openCover.f i ≫
        projectiveStructureMap k n) := by
    simpa only [Scheme.AffineOpenCover.openCover_f,
      ProjectiveSpace.coordinateAffineOpenCover_f,
      ProjectiveSpace.chartι_structureMap] using hChart
  exact HasRingHomProperty.appTop (P := @Smooth.{u}) _ hLocal

end Variety

end

end LeanVarieties
