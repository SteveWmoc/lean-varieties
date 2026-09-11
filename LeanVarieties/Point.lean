import LeanVarieties.Properties

/-!
# The base point as a variety

The scheme `Spec k` over itself is the simplest variety over a field `k`.
Its structural morphism is the identity, so it is both smooth and proper.
-/

namespace LeanVarieties

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Variety

variable (k : Type u) [Field k]

/-- The base point `Spec k`, regarded as a variety over `k`. -/
def point : Variety k :=
  ofScheme (baseScheme k) (𝟙 (baseScheme k))

@[simp]
lemma point_toScheme : (point k).toScheme = baseScheme k := rfl

@[simp]
lemma point_structureMap : (point k).structureMap = 𝟙 (baseScheme k) := rfl

instance point_isSmooth : (point k).IsSmooth := by
  change Smooth (𝟙 (baseScheme k))
  infer_instance

instance point_isProper : (point k).IsProper := by
  change AlgebraicGeometry.IsProper (𝟙 (baseScheme k))
  infer_instance

end Variety

end

end LeanVarieties
