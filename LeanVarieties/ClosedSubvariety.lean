import LeanVarieties.Projective

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
    (f : X ⟶ Y) [IsClosedImmersion ((forget k).map f)] : X.IsProjective := by
  apply IsProjective.of_closedImmersion ((forget k).map f)
  exact Over.w f.hom

end Variety

namespace ProjectiveVariety

variable {k : Type u} [Field k]

/-- Package the source of a closed immersion into a projective variety as a
projective variety. -/
def ofClosedImmersion {X : Variety k} (Y : ProjectiveVariety k) (f : X ⟶ Y.obj)
    [IsClosedImmersion ((Variety.forget k).map f)] : ProjectiveVariety k :=
  ⟨X, Variety.IsProjective.of_closedImmersion_hom f⟩

@[simp]
lemma ofClosedImmersion_obj {X : Variety k} (Y : ProjectiveVariety k) (f : X ⟶ Y.obj)
    [IsClosedImmersion ((Variety.forget k).map f)] :
    (ofClosedImmersion Y f).obj = X := rfl

end ProjectiveVariety

namespace SmoothProjectiveVariety

variable {k : Type u} [Field k]

/-- Package a smooth variety admitting a closed immersion into a projective
variety as a smooth projective variety. -/
def ofClosedImmersion {X : Variety k} [X.IsSmooth] (Y : ProjectiveVariety k)
    (f : X ⟶ Y.obj) [IsClosedImmersion ((Variety.forget k).map f)] :
    SmoothProjectiveVariety k :=
  ⟨X, ⟨inferInstance, Variety.IsProjective.of_closedImmersion_hom f⟩⟩

@[simp]
lemma ofClosedImmersion_obj {X : Variety k} [X.IsSmooth] (Y : ProjectiveVariety k)
    (f : X ⟶ Y.obj) [IsClosedImmersion ((Variety.forget k).map f)] :
    (ofClosedImmersion Y f).obj = X := rfl

end SmoothProjectiveVariety

end

end LeanVarieties
