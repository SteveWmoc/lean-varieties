import LeanVarieties.ProjectiveCharts
import LeanVarieties.AffineSpace
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.SuccPred
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Affine coordinates on the standard projective charts

The chart where the homogeneous coordinate Xᵢ is nonzero has polynomial
coordinates Xⱼ/Xᵢ for j ≠ i. Dehomogenization (setting Xᵢ = 1) gives the
inverse algebra map. These maps identify each standard chart with affine
n-space, compatibly with the structure maps to Spec k.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

universe u

namespace LeanVarieties.ProjectiveSpace

variable (k : Type u) [Field k] (n : ℕ)

/-- The homogeneous coordinates other than the coordinate inverted on a chart. -/
abbrev ChartIndex (i : ULift.{u} (Fin (n + 1))) : Type u := {j // j ≠ i}

/-- Polynomial coordinates on the chart where Xᵢ is nonzero. -/
abbrev ChartPolynomial (i : ULift.{u} (Fin (n + 1))) : Type u :=
  MvPolynomial (ChartIndex n i) k

private abbrev ChartLocalization (i : ULift.{u} (Fin (n + 1))) :=
  Localization.Away (coordinate k n i)

private def chartFraction (i : ULift.{u} (Fin (n + 1))) (d : ℕ)
    (p : CoordinateRing k n) (hp : p.IsHomogeneous d) : ChartRing k n i :=
  HomogeneousLocalization.Away.mk (grading k n) (coordinate_mem k n i) d p
    (by simpa only [smul_eq_mul, mul_one] using hp)

private lemma chartFraction_val_mul (i : ULift.{u} (Fin (n + 1))) (d : ℕ)
    (p : CoordinateRing k n) (hp : p.IsHomogeneous d) :
    (chartFraction k n i d p hp).val *
      algebraMap (CoordinateRing k n) (ChartLocalization k n i) (coordinate k n i ^ d) =
        algebraMap (CoordinateRing k n) (ChartLocalization k n i) p := by
  change Localization.mk p ⟨coordinate k n i ^ d, ⟨d, rfl⟩⟩ * _ = _
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

/-- The degree-zero homogeneous fraction Xⱼ/Xᵢ, including the value 1 when j = i. -/
def coordinateRatio (i j : ULift.{u} (Fin (n + 1))) : ChartRing k n i :=
  chartFraction k n i 1 (coordinate k n j) (coordinate_mem k n j)

private lemma coordinateRatio_val_mul (i j : ULift.{u} (Fin (n + 1))) :
    (coordinateRatio k n i j).val *
      algebraMap (CoordinateRing k n) (ChartLocalization k n i) (coordinate k n i) =
        algebraMap (CoordinateRing k n) (ChartLocalization k n i) (coordinate k n j) := by
  simpa only [pow_one] using
    chartFraction_val_mul k n i 1 (coordinate k n j) (coordinate_mem k n j)

@[simp]
lemma coordinateRatio_self (i : ULift.{u} (Fin (n + 1))) :
    coordinateRatio k n i i = 1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate k n i))
  change Localization.mk (coordinate k n i) ⟨coordinate k n i ^ 1, ⟨1, rfl⟩⟩ = 1
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp

/-- Substitute the affine coordinate ratios into a polynomial. -/
def chartPolynomialToRing (i : ULift.{u} (Fin (n + 1))) :
    ChartPolynomial k n i →ₐ[k] ChartRing k n i :=
  MvPolynomial.aeval fun j => coordinateRatio k n i j.val

@[simp]
lemma chartPolynomialToRing_X (i : ULift.{u} (Fin (n + 1))) (j : ChartIndex n i) :
    chartPolynomialToRing k n i (MvPolynomial.X j) = coordinateRatio k n i j.val :=
  MvPolynomial.aeval_X _ _

/-- Set Xᵢ to 1 and retain the other variables. -/
def dehomogenize (i : ULift.{u} (Fin (n + 1))) :
    CoordinateRing k n →ₐ[k] ChartPolynomial k n i :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

@[simp]
lemma dehomogenize_coordinate_self (i : ULift.{u} (Fin (n + 1))) :
    dehomogenize k n i (coordinate k n i) = 1 := by
  simp [dehomogenize, coordinate]

@[simp]
lemma dehomogenize_coordinate (i : ULift.{u} (Fin (n + 1))) (j : ChartIndex n i) :
    dehomogenize k n i (coordinate k n j.val) = MvPolynomial.X j := by
  simp [dehomogenize, coordinate, j.property]

private def chartRingToLocalization (i : ULift.{u} (Fin (n + 1))) :
    ChartRing k n i →ₐ[k] ChartLocalization k n i where
  __ := algebraMap (ChartRing k n i) (ChartLocalization k n i)
  commutes' r := by
    change Localization.mk (algebraMap k (CoordinateRing k n) r) 1 =
      algebraMap k (ChartLocalization k n i) r
    exact Localization.mk_algebraMap r

private def dehomogenizeLocalization (i : ULift.{u} (Fin (n + 1))) :
    ChartLocalization k n i →ₐ[k] ChartPolynomial k n i :=
  IsLocalization.Away.liftAlgHom (coordinate k n i)
    (show IsUnit (dehomogenize k n i (coordinate k n i)) by simp)

private lemma dehomogenizeLocalization_algebraMap (i : ULift.{u} (Fin (n + 1)))
    (p : CoordinateRing k n) :
    dehomogenizeLocalization k n i
      (algebraMap (CoordinateRing k n) (ChartLocalization k n i) p) =
        dehomogenize k n i p := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- Dehomogenization descends to the degree-zero homogeneous localization. -/
def chartRingToPolynomial (i : ULift.{u} (Fin (n + 1))) :
    ChartRing k n i →ₐ[k] ChartPolynomial k n i :=
  (dehomogenizeLocalization k n i).comp (chartRingToLocalization k n i)

private lemma chartRingToPolynomial_fraction (i : ULift.{u} (Fin (n + 1)))
    (d : ℕ) (p : CoordinateRing k n) (hp : p.IsHomogeneous d) :
    chartRingToPolynomial k n i (chartFraction k n i d p hp) =
      dehomogenize k n i p := by
  have h := congrArg (dehomogenizeLocalization k n i)
    (chartFraction_val_mul k n i d p hp)
  simpa only [map_mul, dehomogenizeLocalization_algebraMap, map_pow,
    dehomogenize_coordinate_self, one_pow, mul_one] using h

@[simp]
lemma chartRingToPolynomial_ratio (i : ULift.{u} (Fin (n + 1))) (j : ChartIndex n i) :
    chartRingToPolynomial k n i (coordinateRatio k n i j.val) = MvPolynomial.X j := by
  rw [coordinateRatio, chartRingToPolynomial_fraction, dehomogenize_coordinate]

private lemma homogeneous_eval₂_mul {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    (f : R →+* S) (g : σ → S) (r : S) :
    p.eval₂ f (fun j => r * g j) = r ^ d * p.eval₂ f g := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hm]
  ac_rfl

private lemma aeval_coordinateRatio (i : ULift.{u} (Fin (n + 1)))
    (d : ℕ) (p : CoordinateRing k n) (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (coordinateRatio k n i) p = chartFraction k n i d p hp := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate k n i))
  change chartRingToLocalization k n i (MvPolynomial.aeval (coordinateRatio k n i) p) =
    Localization.mk p ⟨coordinate k n i ^ d, ⟨d, rfl⟩⟩
  rw [MvPolynomial.comp_aeval_apply, Localization.mk_eq_mk',
    IsLocalization.eq_mk'_iff_mul_eq]
  let f := algebraMap (CoordinateRing k n) (ChartLocalization k n i)
  have hscale := homogeneous_eval₂_mul hp (algebraMap k (ChartLocalization k n i))
    (fun j => (coordinateRatio k n i j).val) (f (coordinate k n i))
  have hvar (j : ULift.{u} (Fin (n + 1))) :
      f (coordinate k n i) * (coordinateRatio k n i j).val = f (coordinate k n j) := by
    rw [mul_comm]
    exact coordinateRatio_val_mul k n i j
  simp only [hvar] at hscale
  have heval :
      (MvPolynomial.aeval (fun j => f (coordinate k n j)) :
        CoordinateRing k n →ₐ[k] ChartLocalization k n i) =
          IsScalarTower.toAlgHom k (CoordinateRing k n) (ChartLocalization k n i) := by
    ext j
    simp [coordinate, f]
  change MvPolynomial.aeval (fun j => (coordinateRatio k n i j).val) p *
    f (coordinate k n i ^ d) = f p
  rw [map_pow, mul_comm]
  exact hscale.symm.trans (AlgHom.congr_fun heval p)

private lemma chartPolynomialToRing_dehomogenize (i : ULift.{u} (Fin (n + 1))) :
    (chartPolynomialToRing k n i).comp (dehomogenize k n i) =
      MvPolynomial.aeval (coordinateRatio k n i) := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [dehomogenize, coordinateRatio_self]
  · simp [dehomogenize, h]

/-- The chart coordinate ring is a polynomial k-algebra in the remaining coordinates. -/
def chartRingEquivPolynomial (i : ULift.{u} (Fin (n + 1))) :
    ChartRing k n i ≃ₐ[k] ChartPolynomial k n i :=
  AlgEquiv.ofAlgHom (chartRingToPolynomial k n i) (chartPolynomialToRing k n i)
    (by ext j; simp)
    (by
      apply AlgHom.ext
      intro z
      obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
        (grading k n) (coordinate_mem k n i) z
      have hp' : p.IsHomogeneous d := by
        simpa only [smul_eq_mul, mul_one] using hp
      change chartPolynomialToRing k n i
        (chartRingToPolynomial k n i (chartFraction k n i d p hp')) =
          chartFraction k n i d p hp'
      rw [chartRingToPolynomial_fraction]
      change ((chartPolynomialToRing k n i).comp (dehomogenize k n i)) p = _
      rw [chartPolynomialToRing_dehomogenize]
      exact aeval_coordinateRatio k n i d p hp')

@[simp]
lemma chartRingEquivPolynomial_symm_X (i : ULift.{u} (Fin (n + 1)))
    (j : ChartIndex n i) :
    (chartRingEquivPolynomial k n i).symm (MvPolynomial.X j) =
      coordinateRatio k n i j.val :=
  chartPolynomialToRing_X k n i j

@[simp]
lemma chartRingEquivPolynomial_ratio (i : ULift.{u} (Fin (n + 1)))
    (j : ChartIndex n i) :
    chartRingEquivPolynomial k n i (coordinateRatio k n i j.val) = MvPolynomial.X j :=
  chartRingToPolynomial_ratio k n i j

/-- List the remaining coordinates in their original order, skipping i. -/
def chartIndexEquiv (i : ULift.{u} (Fin (n + 1))) :
    ULift.{u} (Fin n) ≃ ChartIndex n i :=
  Equiv.ofBijective
    (fun j => ⟨⟨i.down.succAbove j.down⟩, by
      intro h
      exact Fin.succAbove_ne i.down j.down (congrArg ULift.down h)⟩)
    (by
      constructor
      · intro a b h
        apply ULift.ext
        apply Fin.succAbove_right_injective (p := i.down)
        exact congrArg (fun j : ChartIndex n i => j.val.down) h
      · intro j
        have h : j.val.down ≠ i.down := by
          intro h
          apply j.property
          apply ULift.ext
          exact h
        obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
        refine ⟨⟨a⟩, ?_⟩
        apply Subtype.ext
        apply ULift.ext
        exact ha)

/-- Reindex the polynomial chart coordinates by Fin n. -/
def chartRingEquivAffine (i : ULift.{u} (Fin (n + 1))) :
    ChartRing k n i ≃ₐ[k] MvPolynomial (ULift.{u} (Fin n)) k :=
  (chartRingEquivPolynomial k n i).trans
    (MvPolynomial.renameEquiv k (chartIndexEquiv n i).symm)

/-- The spectrum of each standard chart ring is affine n-space over k. -/
def chartAffineSpaceIso (i : ULift.{u} (Fin (n + 1))) :
    chartScheme k n i ≅ Variety.affineScheme k n :=
  Scheme.Spec.mapIso (chartRingEquivAffine k n i).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).symm

@[reassoc (attr := simp)]
lemma chartAffineSpaceIso_hom_structureMap (i : ULift.{u} (Fin (n + 1))) :
    (chartAffineSpaceIso k n i).hom ≫
        (Variety.affineSpace (k := k) n).structureMap = chartStructureMap k n i := by
  change (Spec.map (CommRingCat.ofHom (chartRingEquivAffine k n i).symm.toRingHom) ≫
    (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).inv) ≫
      (Variety.affineScheme k n ↘ baseScheme k) = _
  rw [Category.assoc, AlgebraicGeometry.AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  congr 1
  ext r
  exact (chartRingEquivAffine k n i).symm.commutes r

/-- Each standard open of projective n-space is isomorphic to affine n-space. -/
def coordinateOpenIsoAffineSpace (i : ULift.{u} (Fin (n + 1))) :
    (coordinateOpen k n i).toScheme ≅ Variety.affineScheme k n :=
  coordinateOpenIsoSpec k n i ≪≫ chartAffineSpaceIso k n i

@[reassoc (attr := simp)]
lemma coordinateOpenIsoAffineSpace_hom_structureMap (i : ULift.{u} (Fin (n + 1))) :
    (coordinateOpenIsoAffineSpace k n i).hom ≫
        (Variety.affineSpace (k := k) n).structureMap =
      (coordinateOpen k n i).ι ≫ Variety.projectiveStructureMap k n := by
  change ((coordinateOpenIsoSpec k n i).hom ≫ (chartAffineSpaceIso k n i).hom) ≫ _ = _
  rw [Category.assoc, chartAffineSpaceIso_hom_structureMap,
    ← chartι_structureMap, ← Category.assoc]
  congr 1
  rw [← coordinateOpenIsoSpec_inv_ι]
  simp

/-- The standard chart embedding, with affine n-space as its source. -/
def affineChartι (i : ULift.{u} (Fin (n + 1))) :
    Variety.affineScheme k n ⟶ Variety.projectiveScheme k n :=
  (chartAffineSpaceIso k n i).inv ≫ chartι k n i

instance affineChartι_isOpenImmersion (i : ULift.{u} (Fin (n + 1))) :
    IsOpenImmersion (affineChartι k n i) := by
  dsimp only [affineChartι]
  infer_instance

@[reassoc (attr := simp)]
lemma affineChartι_structureMap (i : ULift.{u} (Fin (n + 1))) :
    affineChartι k n i ≫ Variety.projectiveStructureMap k n =
      (Variety.affineSpace (k := k) n).structureMap := by
  rw [affineChartι, Category.assoc, chartι_structureMap,
    ← chartAffineSpaceIso_hom_structureMap]
  simp

end LeanVarieties.ProjectiveSpace
