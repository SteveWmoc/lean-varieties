# Projective space over a field

PR #6 constructs projective `n`-space as a proper variety over an arbitrary
field, using the pinned mathlib v4.33.0 projective-spectrum API.

## Construction

For `k : Type u` and `n : ℕ`, the homogeneous coordinate ring is

```lean
MvPolynomial (ULift.{u} (Fin (n + 1))) k
```

There are `n + 1` homogeneous coordinates. Every variable has degree one.
The `ULift` keeps the index type in the same universe as the coefficient
field, as in the affine-space API.

`ProjectiveSpace.grading` uses `MvPolynomial.homogeneousSubmodule`.
The named grading instance is restricted to this coordinate-ring family;
it does not declare a preferred grading for every multivariate polynomial ring.

`Variety.projectiveScheme k n` is mathlib's `Proj` of this grading.

## The map to the base field

Mathlib supplies a morphism from `Proj` to the spectrum of the degree-zero
ring. To turn it into a variety over `k`, this PR proves that the coefficient
map is a ring equivalence:

```lean
ProjectiveSpace.degreeZeroEquiv k n :
  k ≃+* (ProjectiveSpace.grading k n 0)
```

Injectivity follows by taking constant coefficients. Surjectivity follows
because a homogeneous polynomial of degree zero is constant. The equivalence
therefore identifies the correct coefficient field, rather than selecting an
unrelated isomorphism.

Applying `Spec` gives `ProjectiveSpace.degreeZeroSpecIso`.
The structural morphism is `Proj.toSpecZero` followed by this scheme
isomorphism. A simp lemma records that the isomorphism's forward map is
`Spec.map` of the coefficient algebra map.

## Properness and the variety API

The coordinate ring is finitely generated over `k`, hence over its
degree-zero ring using the compatible scalar tower. Mathlib then proves
`Proj.toSpecZero` proper. Composing with the base isomorphism preserves
properness and supplies the finite-type, quasi-compactness, and separatedness
needed by `Variety.ofScheme`.

The exported API includes:

- `Variety.projectiveScheme k n`;
- `Variety.projectiveStructureMap k n`;
- `Variety.projectiveSpace (k := k) n : Variety k`;
- simp lemmas for the underlying scheme and structural morphism;
- `Variety.projectiveSpace_isProper`.

All definitions and proofs include `n = 0` and arbitrary field universes.

## Next boundary

This slice establishes projective space and properness. It does not yet
define projectivity for a general variety. That property will require a
closed immersion over the base into some projective space; properness alone
does not express that condition.

The standard affine charts, smoothness of projective space, its dimension,
and the isomorphism between projective zero-space and the base point are
subsequent results. No dimension theorem is implicit in the parameter name.
