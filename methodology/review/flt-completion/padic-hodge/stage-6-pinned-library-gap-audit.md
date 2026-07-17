# Pinned-library gap audit after the Tier-1 weight boundary

Date: 2026-07-17  
Repository checkpoint inspected: `dbc66d5b7f56171b16c3fed9410d7c57ae721afa`  
Pinned Mathlib: `a3364faec42918fcd84a03a255b50570129f9ead`  
Mode: read-only library/source audit; no graph mutation and no provider theorem claimed.

## Result

The accepted global-weight, Fontaine--Laffaille interval, unramifiedness, and representation-dual
vocabulary is a genuine buildable boundary. The next p-adic-Hodge layer is not a wrapper around an
existing pinned Mathlib API.

A repository-wide search of `Mathlib/` and `FLT/` for the expected period-ring and representation
vocabulary found no representation-theoretic declarations for:

- `D_cris` or `B_cris`;
- crystalline Galois representations;
- Hodge--Tate representations or Hodge--Tate weight extraction;
- Fontaine--Laffaille modules or a finite-flat-to-crystalline comparison theorem.

The only `crystalline` search hits in Mathlib are unrelated divided-power/crystalline-cohomology
documentation and constructions. No hit supplies Taylor 2018's local Galois-representation
hypotheses.

The relevant FLT primitive that does exist is
`GaloisRep.IsFlatAt` in
`FLT/Deformations/RepresentationTheory/GaloisRep.lean`. It is an integral finite-flat condition:
for every open ideal, the reduced representation must have a flat prolongation represented by a
finite flat Hopf algebra. This is meaningful source vocabulary, but it is not itself crystallinity
of the characteristic-zero generic fibre.

`FLT/KnownIn1980s/EllipticCurves/Flat.lean` contains the intended good-reduction-to-finite-flat
theorem statement and extensive source discussion, but its load-bearing theorem is still admitted.
It also does not construct period rings or prove the finite-flat-to-crystalline comparison needed
by the Taylor 2018 source contract.

## Consequence for the provider graph

The remaining G1/G2/G4/G5/G6/G7 items should not be estimated or scheduled as one ordinary Lean
definition task:

- G1 and G2 require foundational period-ring/Hodge--Tate vocabulary absent from this pin;
- G4 requires a genuine comparison theorem from the repository's integral `IsFlatAt` predicate to
  crystallinity and weight two of the generic fibre;
- G5 requires the global-embedding/local-place and completion indexing bridge;
- G6 and G7 require dual/determinant transport after G1/G2 exist.

A candidate dependency split for independent review is:

1. period-ring and local-representation vocabulary;
2. crystalline and Hodge--Tate predicates plus weight extraction;
3. global-embedding/local-place indexing;
4. finite-flat-to-crystalline/weight-two comparison;
5. duality and determinant-weight transport;
6. assembly into the exact Taylor 2018 p-adic-Hodge contract.

This is only a proposed decomposition. It must be source-reviewed and transitively reduced before
new obligation rows are created. The existing `FLT-MLT-PADIC-HODGE` obligation remains a
definition gap, and the kernel-green Tier-1 vocabulary must not be counted as its discharge.

## Reproduction

```bash
rg -n --glob '*.lean' \
  'D_cris|IsCrystalline|crystalline|HodgeTate|Hodge.Tate|Fontaine.Laffaille|FontaineLaffaille|PeriodRing|B_cris|Bcris' \
  .lake/packages/mathlib/Mathlib FLT

rg -n 'def IsFlatAt|class IsFlatAt|IsFlatAt' \
  FLT/Deformations/RepresentationTheory/GaloisRep.lean FLT

git -C .lake/packages/mathlib rev-parse HEAD
```

The first command returned only unrelated crystalline-cohomology text in Mathlib. The second
locates the finite-flat representation predicate and its current consumers/admitted providers.
