# Standard projective charts as affine space

The standard open D₊(Xᵢ) of projective n-space is affine n-space over k.
The preceding slice identified it with the spectrum of the degree-zero
homogeneous localization. This slice identifies that ring explicitly.

## Coordinates and inverse maps

For a fixed i, `ChartIndex n i` is the set of the other homogeneous
coordinates. `coordinateRatio k n i j` is Xⱼ/Xᵢ, with Xᵢ/Xᵢ = 1.

The polynomial-to-chart map sends each remaining variable to its coordinate
ratio. Its inverse is dehomogenization: set Xᵢ = 1 and retain the other
variables. Dehomogenization extends to the ordinary localization because
it sends Xᵢ to a unit, then restricts to the degree-zero part.

To prove the maps inverse, the central calculation is that evaluating a
homogeneous polynomial p of degree d at the coordinate ratios gives
p/Xᵢ^d. The proof uses the degree of each supported monomial and checks the
identity in the ordinary localization. Every element of the homogeneous
localization has such a fraction representation.

`chartRingEquivPolynomial` packages the result as a k-algebra equivalence.
The generator formulas are available as simp lemmas.

## Scheme-level API

`chartIndexEquiv` orders the remaining coordinates using Fin.succAbove,
skipping i. It works uniformly when n = 0 as well.

`chartRingEquivAffine` reindexes the polynomial ring by ULift (Fin n).
Applying Spec and mathlib's affine-space comparison gives:

- `chartAffineSpaceIso`: the chart spectrum is isomorphic to affine n-space;
- `coordinateOpenIsoAffineSpace`: D₊(Xᵢ) is isomorphic to affine n-space;
- `affineChartι`: the corresponding open immersion from affine n-space
  into projective n-space.

All three constructions have explicit compatibility lemmas for their
structure maps to Spec k. Thus the isomorphisms preserve the base field,
and can be used in the over-category API.

## Scope

This slice supplies the coordinate identifications. The next step is to
deduce smoothness of projective space from its standard affine cover.
Transition maps and gluing formulas are also available as future work.

The Lean and mathlib versions remain pinned to v4.33.0. The root module
imports the new file so CI checks all definitions and proofs with warnings
treated as errors.
