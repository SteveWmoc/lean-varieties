# Closed subvarieties of fixed dimension

The fixed-dimension API now connects to the closed-immersion constructors:

```lean
SmoothProjectiveVarietyOfDimension.ofClosedImmersion
SmoothProjectiveVarietyOfDimension.ofProjectiveSpace
```

The first takes a variety `X` with a witness of `X.IsSmoothOfDimension n`,
a projective variety `Y`, and a variety morphism `f : X ⟶ Y.obj` whose
underlying scheme morphism is a closed immersion. It returns an object of
`SmoothProjectiveVarietyOfDimension k n` with underlying variety `X`.

The second specializes this construction to an embedding into projective
`m`-space. The source dimension `n` and ambient dimension `m` are independent
parameters. This supports, for example, packaging a smooth curve embedded
in projective space once its smoothness and dimension have been established.

For a packaged source `X : SmoothVarietyOfDimension k n`, the existing
instance supplies the dimension witness automatically:

```lean
open CategoryTheory AlgebraicGeometry
open LeanVarieties

noncomputable example {k : Type u} [Field k] {n : ℕ}
    (X : SmoothVarietyOfDimension k n) (m : ℕ)
    (f : X.obj ⟶ Variety.projectiveSpace (k := k) m)
    [IsClosedImmersion f.hom.left] : SmoothProjectiveVarietyOfDimension k n :=
  SmoothProjectiveVarietyOfDimension.ofProjectiveSpace (n := n) m f
```

Both constructors have `_obj` simp lemmas identifying the underlying variety.
Smoothness and source dimension remain explicit hypotheses; projectivity
comes from the closed immersion. Neither constructor infers the source
dimension from the ambient space. No positivity assumption on `n` is needed.
