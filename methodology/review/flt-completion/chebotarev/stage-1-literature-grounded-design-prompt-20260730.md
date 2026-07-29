# Literature-grounded design: rank-two Chebotarev comparison

Work read-only. Do not edit the repository. Independently design the smallest
sound implementation increment for `FLT-CHEBOTAREV` after commit `8929b77`.

First inspect the exact Lean types and graph. Then read these retrieved sources:

- `SRC-013-gee-2022.qmd`, around lines 312–344: Fact 2.27 and its compatible-
  system consequence;
- `SRC-016-taylor-2018.qmd`, around lines 680–690: the dense-Frobenius trace
  comparison argument;
- `SRC-019-wiese-galois-representations.qmd`, around lines 361–415: finite
  Chebotarev and density in finite quotients.

The files are under:

`/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/`

The encoded family is `GaloisRepFamily ℚ E 2`. Separate these authorities:

- the number-theoretic density theorem;
- deterministic topology/conjugacy/continuity adapters;
- characteristic-polynomial equality on all Galois elements;
- the already proved rank-two Brauer–Nesbitt terminal.

Return exact source-to-Lean hypothesis translation, an acyclic sublemma graph,
candidate signatures, counterexample/normalization checks, T2 versus T3 axiom
policy, and the smallest vertical slice worth implementing now. Explicitly test
whether a union of conjugacy classes—not merely chosen Frobenius elements—is the
dense set, how finite exceptional places are removed, and how local Frobenius is
mapped into the global absolute Galois group.

Do not claim that the literature is itself a Lean proof. Do not hide the density
theorem inside a representation-comparison assumption, and do not claim
Chebotarev or FLT completion.
