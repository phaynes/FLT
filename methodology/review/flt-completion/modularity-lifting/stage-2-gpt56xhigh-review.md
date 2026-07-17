# Stage 2 GPT-5.6 xhigh independent review — modularity lifting

## Verdict: REVISE

Classification: substantive mathematical and statement-level. The Taylor route is not refuted, and
the repository/source split is correct in principle, but the proposed interfaces are not yet source-
or consumer-exact.

## Findings

- Taylor's at-ell automorphic hypothesis is correctly owned by the RACAR witness: every local
  component `pi_v` for `v | ell` is unramified. The theorem conclusion remains level-free GL2
  automorphy and is not equivalent to `IsAutomorphicOfLevel`.
- `SourceHypotheses` omits the chosen complex embedding and explicit coefficient ownership. It must
  expose one finite coefficient ring `O`, stable lattice, and a single selected semisimplified
  residual model shared by residual agreement and cyclotomic irreducibility. Hidden existential
  reductions could otherwise differ. The reviewed coefficient boundary requires explicit `O`; the
  valuation ring of `AlgebraicClosure ℚ_[ell]` is not a DVR/Noetherian substitute.
- The p-adic-Hodge boundary remains unresolved. Taylor uses global embeddings, a single global
  integer `a`, and the exact interval `[a, a + ell - 2]`. The earlier diameter-style field is not
  source-exact, and field-unramifiedness must be explicit.
- The dual/sign issue is load-bearing. Taylor's applications use the dual Tate-module
  representation, while the repository consumers use cyclotomic determinant on the undualized
  representation. The bridge must expose dual/twist orientation, determinant transport,
  flat-to-crystalline transport, and Hodge–Tate sign conversion.
- `SelectedGood` omitted `supportAwayEll : ∀ w ∈ S, ↑ell ∉ w.asIdeal`. It also did not expose the
  separate cyclotomic-degree hypothesis required by `IsAutomorphicOfLevel`.
- The proposed tame quotient was placed on an integral representation, while the live
  `cyclic_base_change` consumer requires it on the `AlgebraicClosure ℚ_[ell]` generic fibre. It also
  strengthened `BlueprintSGood.traceOnJ` without a bridge or a representability theorem.
- Proposed graph consumers are not yet Lean consumers. The future Hecke signature omits explicit
  `ell`, and deformation/local-Galois consumers still use the blueprint trace condition. The
  source theorem must not term-depend on repository-specific `BlueprintSGood` or
  `IsAutomorphicOfLevel`.

## Probe result

The proposed `SelectedGood` can be made to elaborate and audits to the standard trio, but this is
only syntactic success and the statement is not honest enough to freeze.

The reviewed next unit is `FLTMethodology.Probes.SelectedGoodRepositoryBoundary`, containing only:

1. `SelectedGoodRepository`, extending `BlueprintSGood ell rho S` with
   `supportAwayEll : ∀ w ∈ S, ↑ell ∉ w.asIdeal`;
2. `HasGenericTameRankOneQuotient ell rho S`, matching `cyclic_base_change.hrhoTame` exactly over
   `AlgebraicClosure ℚ_[ell]`;
3. standard-trio `#print axioms` checks.

Do not state a repository-to-source bridge until explicit coefficient data, the generic-fibre/dual
orientation, and the repaired p-adic-Hodge interface have landed.

## Typed Fable decision

`KEEP`: difficulty 10 and the review found substantive missing ownership, wrong representation
layer, source-hypothesis omissions, and an unresolved dual/sign bridge.

This review was read-only and made no promotion.
