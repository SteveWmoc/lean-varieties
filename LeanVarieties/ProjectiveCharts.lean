import LeanVarieties.ProjectiveSpace
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Standard affine charts of projective space

The coordinate basic opens cover projective space because the homogeneous
coordinates generate the irrelevant ideal. Each open is canonically the
spectrum of the degree-zero homogeneous localization at its coordinate.

This file packages the resulting finite affine open cover and records the
compatibility of every chart map with the structural morphism to `Spec k`.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace ProjectiveSpace

variable (k : Type u) [Field k] (n : ℕ)

/-- A homogeneous coordinate of projective `n`-space. -/
abbrev coordinate (i : ULift.{u} (Fin (n + 1))) : CoordinateRing k n :=
  MvPolynomial.X i

/-- Every homogeneous coordinate has degree one. -/
lemma coordinate_mem (i : ULift.{u} (Fin (n + 1))) :
    coordinate k n i ∈ grading k n 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The homogeneous coordinates generate the irrelevant ideal. -/
lemma irrelevant_eq_span_coordinates :
    (HomogeneousIdeal.irrelevant (grading k n)).toIdeal =
      Ideal.span (Set.range (coordinate k n)) := by
  apply le_antisymm
  · rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro d hd p hp
    have hp' : p.IsHomogeneous d := hp
    have hmem : p ∈ MvPolynomial.idealOfVars (ULift.{u} (Fin (n + 1))) k ^ 1 := by
      rw [MvPolynomial.mem_pow_idealOfVars_iff']
      intro m hm
      exact hp'.coeff_eq_zero (ne_of_lt (lt_of_lt_of_le hm hd))
    simpa only [pow_one] using hmem
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    exact HomogeneousIdeal.mem_irrelevant_of_mem (grading k n)
      Nat.zero_lt_one (coordinate_mem k n i)

/-- The standard open `D₊(Xᵢ)` where the `i`th coordinate does not vanish. -/
def coordinateOpen (i : ULift.{u} (Fin (n + 1))) :
    (Variety.projectiveScheme k n).Opens :=
  Proj.basicOpen (grading k n) (coordinate k n i)

/-- The standard coordinate opens cover projective space. -/
lemma iSup_coordinateOpen_eq_top : ⨆ i, coordinateOpen k n i = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grading k n) (coordinate k n)
    (irrelevant_eq_span_coordinates k n).le

/-- Each standard coordinate open is affine. -/
lemma isAffineOpen_coordinateOpen (i : ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (coordinateOpen k n i) :=
  Proj.isAffineOpen_basicOpen (grading k n) (coordinate k n i)
    (coordinate_mem k n i) Nat.zero_lt_one

/-- The ring of degree-zero fractions with powers of `Xᵢ` as denominators. -/
abbrev ChartRing (i : ULift.{u} (Fin (n + 1))) : Type u :=
  HomogeneousLocalization.Away (grading k n) (coordinate k n i)

/-- The coefficient field acts on each chart ring through the degree-zero ring. -/
instance chartRingAlgebra (i : ULift.{u} (Fin (n + 1))) :
    Algebra k (ChartRing k n i) :=
  ((algebraMap (grading k n 0) (ChartRing k n i)).comp
    (algebraMap k (grading k n 0))).toAlgebra

/-- The chart's field structure agrees with its degree-zero ring structure. -/
instance chartRing_isScalarTower (i : ULift.{u} (Fin (n + 1))) :
    IsScalarTower k (grading k n 0) (ChartRing k n i) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := grading k n 0)
    (A := ChartRing k n i) fun _ => rfl

/-- The affine scheme of a standard coordinate chart. -/
abbrev chartScheme (i : ULift.{u} (Fin (n + 1))) : Scheme.{u} :=
  Spec (.of (ChartRing k n i))

/-- The standard coordinate open is the spectrum of its homogeneous localization. -/
def coordinateOpenIsoSpec (i : ULift.{u} (Fin (n + 1))) :
    (coordinateOpen k n i).toScheme ≅ chartScheme k n i :=
  Proj.basicOpenIsoSpec (grading k n) (coordinate k n i)
    (coordinate_mem k n i) Nat.zero_lt_one

/-- The open immersion of a standard affine chart into projective space. -/
def chartι (i : ULift.{u} (Fin (n + 1))) :
    chartScheme k n i ⟶ Variety.projectiveScheme k n :=
  Proj.awayι (grading k n) (coordinate k n i)
    (coordinate_mem k n i) Nat.zero_lt_one

instance chartι_isOpenImmersion (i : ULift.{u} (Fin (n + 1))) :
    IsOpenImmersion (chartι k n i) := by
  dsimp only [chartι]
  infer_instance

@[simp]
lemma chartι_opensRange (i : ULift.{u} (Fin (n + 1))) :
    (chartι k n i).opensRange = coordinateOpen k n i :=
  Proj.opensRange_awayι (grading k n) (coordinate k n i)
    (coordinate_mem k n i) Nat.zero_lt_one

@[reassoc]
lemma coordinateOpenIsoSpec_inv_ι (i : ULift.{u} (Fin (n + 1))) :
    (coordinateOpenIsoSpec k n i).inv ≫ (coordinateOpen k n i).ι = chartι k n i := rfl

/-- The structural morphism of a chart induced by its coefficient-field map. -/
def chartStructureMap (i : ULift.{u} (Fin (n + 1))) :
    chartScheme k n i ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k n i)))

/-- The chart immersion commutes with the structural morphisms to the base field. -/
@[reassoc (attr := simp)]
lemma chartι_structureMap (i : ULift.{u} (Fin (n + 1))) :
    chartι k n i ≫ Variety.projectiveStructureMap k n = chartStructureMap k n i := by
  dsimp only [chartι, Variety.projectiveStructureMap, chartStructureMap]
  rw [← Category.assoc, Proj.awayι_toSpecZero, degreeZeroSpecIso_hom, ← Spec.map_comp]
  rfl

/-- The finite affine open cover of projective space by its standard coordinates. -/
def coordinateAffineOpenCover : (Variety.projectiveScheme k n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading k n) (coordinate k n)
    (m := fun _ => 1) (coordinate_mem k n) (fun _ => Nat.zero_lt_one)
    (irrelevant_eq_span_coordinates k n).le

@[simp]
lemma coordinateAffineOpenCover_X (i : ULift.{u} (Fin (n + 1))) :
    (coordinateAffineOpenCover k n).X i = CommRingCat.of (ChartRing k n i) := rfl

@[simp]
lemma coordinateAffineOpenCover_f (i : ULift.{u} (Fin (n + 1))) :
    (coordinateAffineOpenCover k n).f i = chartι k n i := rfl

instance coordinateAffineOpenCover_fintype :
    Fintype (coordinateAffineOpenCover k n).I₀ :=
  inferInstanceAs (Fintype (ULift.{u} (Fin (n + 1))))

/-- The standard cover has exactly `n + 1` indexed charts. -/
@[simp]
lemma card_coordinateAffineOpenCover :
    Fintype.card (coordinateAffineOpenCover k n).I₀ = n + 1 := by
  change Fintype.card (ULift.{u} (Fin (n + 1))) = n + 1
  simp

end ProjectiveSpace

end

end LeanVarieties
