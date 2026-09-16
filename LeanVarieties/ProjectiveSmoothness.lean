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
  change Smooth (projectiveStructureMap k n)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @Smooth) (ProjectiveSpace.coordinateOpen k n)
    (ProjectiveSpace.iSup_coordinateOpen_eq_top k n)]
  intro i
  rw [← ProjectiveSpace.coordinateOpenIsoAffineSpace_hom_structureMap]
  infer_instance

end Variety

end

end LeanVarieties
