# Taylor 2018 modularity-lifting source boundary

Selected source: Richard Taylor's 2018 *Automorphy Lifting* lectures, notes by Dan Dore and Tony
Feng, Theorem 2.1.1, printed page 12. This document records a mathematical contract; it is not a
Lean theorem and does not claim that the required vocabulary has been formalized.

## Exact source shape

Fix a prime `ell > 2`, an identification between the algebraic `ell`-adic and complex closures, a
totally real field `F`, and a regular algebraic two-dimensional `ell`-adic representation `r` of
the absolute Galois group of `F`.

Required data and hypotheses:

1. a regular algebraic cuspidal automorphic representation `pi` of `GL2` over `F`;
2. an isomorphism between the semisimplified residual representations attached to `pi` and `r`;
3. matching Hodge--Tate weights at every embedding;
4. irreducibility of the residual representation after restriction to `F(zeta_ell)`;
5. `ell` unramified in `F`;
6. crystallinity of `r` at every place above `ell`;
7. unramifiedness of `pi_v` at every place `v | ell`;
8. all Hodge--Tate weights contained in a Fontaine--Laffaille interval of length `ell - 1`.

Conclusion: `r` is automorphic in the source's level-free GL2/RACAR sense.

## Deliberate separations

- `IsAutomorphicOfLevel ell ... empty` does not encode item 7: the repository predicate controls
  places away from `ell`.
- `GaloisRep.IsAutomorphicOfLevel ... S` is not the source conclusion. It belongs to a separate
  derived theorem using attached-representation, local-global, Hecke, patching, and
  Jacquet--Langlands bridges.
- A generic integral-coefficient representation is not definitionally the source representation.
  Stable-lattice choice, residual reduction, semisimplification, and scalar extension are explicit
  obligations.
- `GaloisRep.IsFlatAt` is not definitionally the source's crystalline/Hodge--Tate condition. The
  weight-two comparison is an explicit p-adic Hodge theorem.

## Lean signature stop point

The current repository can typecheck `GaloisRep`, `GaloisRep.IsFlatAt`,
`GaloisRep.IsAutomorphicOfLevel`, and `ker_RtoT_le_nilradical`. It does not yet provide the
source-faithful coefficient/lattice/semisimplification package, crystalline and Hodge--Tate
predicates, or a totally-real RACAR object with attached representation. Therefore an exact Lean
signature for Theorem 2.1.1 cannot yet elaborate honestly.

`FLTMethodology.Probes.MLTSourceBoundary` now contains a kernel-clean
`FLTMethodology.Taylor2018.HasIntegralModel` definition matching the existing integral-model shape.
Its axiom audit is the standard trio. This is a banked partial signature, not closure of
`FLT-MLT-COEFFICIENTS`: residual reduction, semisimplification, and lattice-independence remain.

The next coefficient-boundary tranche adds three provisional, kernel-clean relations:

- `IsSemisimplifiedResidualModel`, requiring semisimplicity plus equality of characteristic
  polynomials with the reduction of the chosen integral model for every Galois element;
- `SemisimpleResidualEquivalent`, requiring an actual linear equivalence conjugating the two
  selected residual models; and
- `ResidualModelsAgreeAfterExtension`, comparing models over different residue fields only after
  both have been extended to a common coefficient field.

These relations do **not** construct a semisimplification, prove lattice independence, or close
`FLT-MLT-COEFFICIENTS`; those remain named dependencies before the Taylor source contract can be
frozen.

The first three W00 definition nodes are:

1. `FLT-MLT-COEFFICIENTS`;
2. `FLT-MLT-PADIC-HODGE`;
3. `FLT-RACAR-DEF`.

Only after those signatures are kernel-green may `FLT-MLT-SOURCE` be frozen. W04--W06 construction
remains blocked until that source contract and `FLT-SGOOD-SELECTED` elaborate and pass the review
gate.
