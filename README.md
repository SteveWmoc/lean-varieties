# lean-varieties

A Lean 4 API for algebraic varieties over a field, built on mathlib's scheme-theoretic foundations.

The immediate goal is to develop a small, reusable varieties layer without duplicating mathlib's algebraic-geometry infrastructure. A downstream motivation is the formal statement of the Hodge conjecture.

## Mathematical scope

`Variety k` is the full subcategory of schemes over `Spec k` whose structural
morphism is locally of finite type, quasi-compact, and separated: a separated
scheme of finite type over a field. Reducedness and irreducibility are not
implicit assumptions. Morphisms automatically commute with the maps to the
base field. See the [semantic convention](docs/0001-variety-semantics.md).

The library currently provides:

- Smooth, proper, projective, and smooth projective varieties, with complex
  specializations and categories of fixed smooth relative dimension.
- The base point, affine `n`-space, and projective `n`-space over any field,
  including `n = 0`; affine and projective spaces are smooth of dimension `n`.
- Standard projective affine charts, explicit polynomial coordinate rings,
  and compatibility of the chart isomorphisms with the base field.
- Projectivity inherited through closed immersions, and constructors that
  package smooth projective sources when smoothness is supplied.
- Transport of smoothness, properness, projectivity, and smooth dimension
  along isomorphisms of varieties.
- Closed subschemes constructed from ideal-sheaf data, their canonical closed
  immersions, and contravariant functoriality with respect to ideal inclusion.
  The zero ideal recovers the ambient variety by a canonical isomorphism.
  Ideal sums define scheme-theoretic intersections, with closed-immersion
  projections and unique lifts of compatible maps into both factors.
  These intersections also carry mathlib pullback witnesses and canonical
  comparison isomorphisms to its chosen pullbacks. Canonical symmetry swaps
  their projections; absorption recovers a subscheme already contained in
  the other factor, including self-intersections. Inverse images along variety
  morphisms come with their canonical commuting square and support formula,
  unique compatible lifts, and categorical pullback witnesses. Canonical
  isomorphisms identify inverse images along identities and composites,
  and identify inverse images of intersections with intersections of inverse images.
  Inverse images form a functor on the opposite ideal poset, with natural
  restriction maps and a natural identity comparison.

- Integer algebraic cycles using mathlib’s generic-point representation, finite
  support and finite-sum reconstruction, and effective cycles. Codimension-`p`
  cycles form additive subgroups, using coheight of irreducible closed subsets.
  Additive component projections are idempotent, annihilate distinct degrees,
  and reconstruct each cycle by a finite sum over degrees in `ℕ∞`.

Projectivity means admitting a closed immersion over the base into some finite
projective space; it implies properness. Fixed dimension uses mathlib's
`SmoothOfRelativeDimension`, rather than a general dimension invariant for
singular schemes. Closed subschemes can be singular or nonreduced, so their
smoothness and dimension require separate hypotheses.

Chow groups, analytification, cohomology, Hodge structures, and a statement
of the Hodge conjecture remain outside the API. Reconstruction includes a
possible infinite-codimension component; finiteness of all generator codimensions,
a bundled direct-sum equivalence, and comparisons with other dimension conventions
are not yet proved.

## Build and use

Install [elan](https://github.com/leanprover/elan), then run from this repository:

```sh
lake exe cache get
lake build --wfail
lake lint
```

Lean and mathlib are pinned to **v4.34.1**. `lean-toolchain`, `lakefile.toml`,
and the committed `lake-manifest.json` record the toolchain and dependencies.
Keep those files together when upgrading; ordinary builds do not need
`lake update`.

Import the full API with `import LeanVarieties`, or import individual modules
from the table below. For example:

```lean
import LeanVarieties

open LeanVarieties

noncomputable example : SmoothProjectiveComplexVarietyOfDimension 2 :=
  SmoothProjectiveVarietyOfDimension.projectiveSpace 2

example {k : Type} [Field k] (n : ℕ) :
    (Variety.affineSpace (k := k) n).IsSmoothOfDimension n := inferInstance
```

## Module guide

All module names below have the prefix `LeanVarieties.`.

| Module | Purpose |
| --- | --- |
| [Basic](LeanVarieties/Basic.lean) | Varieties, structure maps, constructors, and forgetful functors |
| [Properties](LeanVarieties/Properties.lean) | Smooth and proper predicates and categories |
| [Point](LeanVarieties/Point.lean) | The smooth proper base point |
| [AffineSpace](LeanVarieties/AffineSpace.lean) | Affine space and smoothness |
| [ProjectiveSpace](LeanVarieties/ProjectiveSpace.lean) | Projective space via `Proj`, and properness |
| [Projective](LeanVarieties/Projective.lean) | Projectivity and smooth projective categories |
| [ProjectiveCharts](LeanVarieties/ProjectiveCharts.lean) | Standard finite affine open cover |
| [ProjectiveChartCoordinates](LeanVarieties/ProjectiveChartCoordinates.lean) | Chart polynomial rings and affine-space isomorphisms |
| [ProjectiveSmoothness](LeanVarieties/ProjectiveSmoothness.lean) | Smoothness from the standard cover |
| [ProjectiveSpaceObjects](LeanVarieties/ProjectiveSpaceObjects.lean) | Projective-space objects in the refined categories |
| [ClosedSubvariety](LeanVarieties/ClosedSubvariety.lean) | Projectivity and packaging through closed immersions |
| [Dimension](LeanVarieties/Dimension.lean) | Fixed smooth relative dimension and forgetful functors |
| [StandardSpaceDimension](LeanVarieties/StandardSpaceDimension.lean) | Dimension witnesses for standard spaces |
| [Isomorphism](LeanVarieties/Isomorphism.lean) | Geometric properties transported along isomorphisms |
| [ClosedSubscheme](LeanVarieties/ClosedSubscheme.lean) | Closed subschemes as varieties over the ambient base |
| [ClosedSubschemeInclusions](LeanVarieties/ClosedSubschemeInclusions.lean) | Canonical inclusions and the ideal-sheaf functor |
| [ClosedSubschemeZero](LeanVarieties/ClosedSubschemeZero.lean) | The zero-ideal subscheme and its ambient isomorphism |
| [ClosedSubschemeIntersection](LeanVarieties/ClosedSubschemeIntersection.lean) | Scheme-theoretic intersections and their universal property |
| [ClosedSubschemePullback](LeanVarieties/ClosedSubschemePullback.lean) | Standard pullback witnesses, comparison isomorphisms, and lift compatibility |
| [ClosedSubschemeIntersectionLaws](LeanVarieties/ClosedSubschemeIntersectionLaws.lean) | Symmetry, absorption, and self-intersection isomorphisms |
| [ClosedSubschemePreimage](LeanVarieties/ClosedSubschemePreimage.lean) | Inverse images, canonical maps, and their underlying closed sets |
| [ClosedSubschemePreimagePullback](LeanVarieties/ClosedSubschemePreimagePullback.lean) | Inverse-image lifts, uniqueness, and the categorical pullback API |
| [ClosedSubschemePreimageComposition](LeanVarieties/ClosedSubschemePreimageComposition.lean) | Identity and composition isomorphisms respecting canonical maps |
| [ClosedSubschemePreimageIntersection](LeanVarieties/ClosedSubschemePreimageIntersection.lean) | Inverse images preserve intersections and their projection maps |
| [ClosedSubschemePreimageFunctor](LeanVarieties/ClosedSubschemePreimageFunctor.lean) | Functorial inverse images, natural restriction, and the natural identity comparison |

| [AlgebraicCycle](LeanVarieties/AlgebraicCycle.lean) | Ungraded integer cycles, finite support, generators, and effectivity |
| [CycleCodimension](LeanVarieties/CycleCodimension.lean) | Codimension via irreducible closed chains and fixed-codimension cycle subgroups |
| [CycleComponents](LeanVarieties/CycleComponents.lean) | Additive codimension projections and finite reconstruction including infinity |

## Documentation and checks

The [documentation index](docs/README.md) links the mathematical design and
construction notes. [CONTRIBUTING.md](CONTRIBUTING.md) describes the development
workflow and lint checks.

CI builds with warnings treated as errors, runs ordinary builtin `lake lint`,
checks that a deliberate unused-variable violation is detected, and uploads
the `lean-code-quality` JSON report. The report must contain zero findings;
report generation alone is not a pass criterion. The selected linters are
those enabled by the pinned Lean/mathlib defaults and source options, not
every optional linter.
