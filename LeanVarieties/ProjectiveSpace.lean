import LeanVarieties.Properties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space as a proper variety

Projective `n`-space over a field `k` is the projective spectrum of the
polynomial ring in `n + 1` variables with its standard grading. The
degree-zero ring is canonically isomorphic to `k`, so mathlib's
`Proj.toSpecZero` gives a structural morphism to `Spec k`.

Mathlib's properness theorem for finitely generated graded rings supplies
properness of this structural morphism and hence the variety conditions.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace ProjectiveSpace

variable (k : Type u) [Field k] (n : ℕ)

/-- The homogeneous coordinate ring of projective `n`-space. -/
abbrev CoordinateRing : Type u :=
  MvPolynomial (ULift.{u} (Fin (n + 1))) k

/-- The standard grading by total degree, with all coordinates of degree one. -/
abbrev grading : ℕ → Submodule k (CoordinateRing k n) :=
  MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k

/-- Use the standard grading for this specific homogeneous coordinate ring. -/
instance gradedAlgebra : GradedAlgebra (grading k n) :=
  MvPolynomial.gradedAlgebra

/-- The coefficient map identifies the base field with the degree-zero ring. -/
def degreeZeroEquiv : k ≃+* (grading k n 0) :=
  RingEquiv.ofBijective (algebraMap k (grading k n 0)) (by
    constructor
    · intro a b h
      have h' := congrArg
        (fun p : grading k n 0 => MvPolynomial.constantCoeff p.1) h
      change MvPolynomial.constantCoeff (MvPolynomial.C a) =
        MvPolynomial.constantCoeff (MvPolynomial.C b) at h'
      simpa only [MvPolynomial.constantCoeff_C] using h'
    · intro p
      refine ⟨p.1.coeff 0, ?_⟩
      apply Subtype.ext
      change MvPolynomial.C (p.1.coeff 0) = p.1
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous
          (ULift.{u} (Fin (n + 1)))).mpr p.2)).symm)

@[simp]
lemma degreeZeroEquiv_apply (a : k) :
    (degreeZeroEquiv k n a : CoordinateRing k n) = MvPolynomial.C a := rfl

/-- Identify the spectrum of the degree-zero ring with the base scheme. -/
def degreeZeroSpecIso : Spec (.of (grading k n 0)) ≅ baseScheme k :=
  Scheme.Spec.mapIso (degreeZeroEquiv k n).toCommRingCatIso.op

@[simp]
lemma degreeZeroSpecIso_hom :
    (degreeZeroSpecIso k n).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (grading k n 0))) := rfl

/-- Finitely many coordinates generate the polynomial ring over its degree-zero ring. -/
instance coordinateRing_finiteType :
    Algebra.FiniteType (grading k n 0) (CoordinateRing k n) := by
  let : IsScalarTower k (grading k n 0) (CoordinateRing k n) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := grading k n 0)
      (A := CoordinateRing k n) fun _ => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    k (grading k n 0) (CoordinateRing k n)

end ProjectiveSpace

namespace Variety

variable (k : Type u) [Field k]

/-- The underlying scheme of projective `n`-space over `k`. -/
abbrev projectiveScheme (n : ℕ) : Scheme.{u} :=
  Proj (ProjectiveSpace.grading k n)

/-- The structural morphism of projective `n`-space to `Spec k`. -/
def projectiveStructureMap (n : ℕ) : projectiveScheme k n ⟶ baseScheme k :=
  Proj.toSpecZero (ProjectiveSpace.grading k n) ≫
    (ProjectiveSpace.degreeZeroSpecIso k n).hom

/-- Projective space is proper over its base field. -/
instance projectiveStructureMap_isProper (n : ℕ) :
    AlgebraicGeometry.IsProper (projectiveStructureMap k n) := by
  dsimp only [projectiveStructureMap]
  infer_instance

variable {k}

/-- Projective `n`-space over `k`, regarded as a variety. -/
def projectiveSpace (n : ℕ) : Variety k :=
  ofScheme (projectiveScheme k n) (projectiveStructureMap k n)

@[simp]
lemma projectiveSpace_toScheme (n : ℕ) :
    (projectiveSpace (k := k) n).toScheme = projectiveScheme k n := rfl

@[simp]
lemma projectiveSpace_structureMap (n : ℕ) :
    (projectiveSpace (k := k) n).structureMap = projectiveStructureMap k n := rfl

instance projectiveSpace_isProper (n : ℕ) :
    (projectiveSpace (k := k) n).IsProper := by
  change AlgebraicGeometry.IsProper (projectiveStructureMap k n)
  infer_instance

end Variety

end

end LeanVarieties
