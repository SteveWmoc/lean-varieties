# Canonical projective-space objects

PR #11 packages projective space into the full subcategories introduced by the
project's projectivity API.

Earlier slices established, for every field `k` and natural number `n`,

- `Variety.projectiveSpace (k := k) n` is projective; and
- `Variety.projectiveSpace (k := k) n` is smooth.

This PR adds the corresponding canonical objects

```lean
ProjectiveVariety.projectiveSpace (k := k) n :
  ProjectiveVariety k

SmoothProjectiveVariety.projectiveSpace (k := k) n :
  SmoothProjectiveVariety k
```

Both definitions are deliberately thin wrappers around
`Variety.projectiveSpace`. Their property fields are discharged entirely from
the existing instances; no new geometric theorem is proved here.

Each constructor has a simp lemma identifying its underlying variety:

```lean
ProjectiveVariety.projectiveSpace_obj
SmoothProjectiveVariety.projectiveSpace_obj
```

The main purpose is API ergonomics. Later constructions aimed at the Hodge
conjecture can now take a canonical smooth projective object directly, without
repackaging smoothness and projectivity at each use site.

Fixed smooth dimension and closed subvariety constructors are now available
in [0013](0013-standard-space-dimension.md) and
[0011](0011-closed-subvarieties.md). A dedicated API for morphisms between
projective spaces, cycles, cohomology, and Hodge structures remains future work.
