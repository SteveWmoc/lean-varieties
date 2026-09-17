import LeanVarieties.Projective
import LeanVarieties.ProjectiveSmoothness

/-!
# Projective space as projective and smooth projective objects

The preceding projective-space development proves the relevant geometric
properties at the level of `Variety k`. This file packages those witnesses as
canonical objects of the full subcategories `ProjectiveVariety k` and
`SmoothProjectiveVariety k`.
-/

namespace LeanVarieties

noncomputable section

universe u

namespace ProjectiveVariety

variable {k : Type u} [Field k]

/-- Projective `n`-space as an object of the category of projective varieties. -/
def projectiveSpace (n : ℕ) : ProjectiveVariety k :=
  ⟨Variety.projectiveSpace (k := k) n, Variety.projectiveSpace_isProjective n⟩

@[simp]
lemma projectiveSpace_obj (n : ℕ) :
    (projectiveSpace (k := k) n).obj = Variety.projectiveSpace (k := k) n := rfl

end ProjectiveVariety

namespace SmoothProjectiveVariety

variable {k : Type u} [Field k]

/-- Projective `n`-space as an object of the category of smooth projective varieties. -/
def projectiveSpace (n : ℕ) : SmoothProjectiveVariety k :=
  ⟨Variety.projectiveSpace (k := k) n,
    ⟨Variety.projectiveSpace_isSmooth n, Variety.projectiveSpace_isProjective n⟩⟩

@[simp]
lemma projectiveSpace_obj (n : ℕ) :
    (projectiveSpace (k := k) n).obj = Variety.projectiveSpace (k := k) n := rfl

end SmoothProjectiveVariety

end

end LeanVarieties
