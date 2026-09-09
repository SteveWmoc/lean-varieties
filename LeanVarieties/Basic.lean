import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Algebraic varieties over a field

This file defines the project's basic notion of an algebraic variety over a field.
A `Variety k` is a separated scheme of finite type over `Spec k`.

Mathlib represents "finite type" by the conjunction of `LocallyOfFiniteType`
and `QuasiCompact`, so both properties are recorded explicitly below.

The implementation is deliberately thin: varieties form the full subcategory of
`Over (Spec k)` cut out by those three properties. In particular, morphisms in
`Variety k` are automatically morphisms over `Spec k`.
-/

namespace LeanVarieties

open CategoryTheory
open AlgebraicGeometry

universe u

/-- The base scheme `Spec k` associated to a field `k`. -/
abbrev baseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of k)

/-- The property defining varieties among schemes over `Spec k`. -/
def isVariety (k : Type u) [Field k] : ObjectProperty (Over (baseScheme k)) :=
  fun X => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsSeparated X.hom

/--
The category of algebraic varieties over a field `k`.

By project convention, these are separated schemes of finite type over `Spec k`.
-/
abbrev Variety (k : Type u) [Field k] :=
  (isVariety k).FullSubcategory

namespace Variety

variable {k : Type u} [Field k]

/-- Regard a variety as its object in the over-category of `Spec k`. -/
abbrev toOver (X : Variety k) : Over (baseScheme k) :=
  X.obj

/-- The underlying scheme of a variety. -/
abbrev toScheme (X : Variety k) : Scheme.{u} :=
  X.obj.left

/-- The structural morphism `X ⟶ Spec k`. -/
abbrev structureMap (X : Variety k) : X.toScheme ⟶ baseScheme k :=
  X.obj.hom

instance (X : Variety k) : LocallyOfFiniteType X.structureMap :=
  X.property.1

instance (X : Variety k) : QuasiCompact X.structureMap :=
  X.property.2.1

instance (X : Variety k) : IsSeparated X.structureMap :=
  X.property.2.2

/-- Construct a variety from an object over `Spec k` carrying the defining properties. -/
def mk (X : Over (baseScheme k)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : Variety k :=
  ⟨X, inferInstance, inferInstance, inferInstance⟩

/-- Construct a variety directly from a scheme and a structural morphism to `Spec k`. -/
def ofScheme (X : Scheme.{u}) (f : X ⟶ baseScheme k) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] : Variety k :=
  mk (Over.mk f)

/-- The inclusion of varieties into schemes over `Spec k`. -/
abbrev inclusion (k : Type u) [Field k] : Variety k ⥤ Over (baseScheme k) :=
  (isVariety k).ι

/-- Forget a variety down to its underlying scheme. -/
abbrev forget (k : Type u) [Field k] : Variety k ⥤ Scheme.{u} :=
  inclusion k ⋙ Over.forget (baseScheme k)

@[simp]
lemma forget_obj (X : Variety k) : (forget k).obj X = X.toScheme := rfl

end Variety

end LeanVarieties
