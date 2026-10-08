# Mathematical documentation

The [project README](../README.md) describes the current API and dependency
versions. [CONTRIBUTING.md](../CONTRIBUTING.md) covers builds and linting.

The numbered notes record the design and successive constructions. References
to individual PRs describe when a feature was introduced; subsequent work is
linked where it resolves an earlier boundary. The semantic convention in ADR
0001 remains the basis of the current API.

| Area | Notes |
| --- | --- |
| Semantics and core category | [0001: Variety convention](0001-variety-semantics.md) |
| Affine space | [0002: Construction](0002-affine-space.md), [0004: Smoothness](0004-affine-space-smoothness.md) |
| Geometric properties | [0003: Smooth and proper](0003-variety-properties.md), [0006: Projective](0006-projective-varieties.md) |
| Projective space | [0005: Construction](0005-projective-space.md), [0007: Charts](0007-projective-charts.md), [0008: Coordinates](0008-projective-chart-coordinates.md), [0009: Smoothness](0009-projective-space-smoothness.md), [0010: Packaged objects](0010-projective-space-objects.md) |
| Fixed smooth dimension | [0012: Categories](0012-smooth-dimension.md), [0013: Standard-space witnesses](0013-standard-space-dimension.md) |
| Closed immersions | [0011: Projectivity and packaging](0011-closed-subvarieties.md), [0014: Fixed-dimension packaging](0014-fixed-dimension-closed-subvarieties.md) |
| Isomorphisms | [0015: Invariance of geometric properties](0015-isomorphism-invariance.md) |
| Closed subschemes | [0016: Construction](0016-closed-subscheme-construction.md), [0017: Inclusions and functoriality](0017-closed-subscheme-inclusions.md) |
