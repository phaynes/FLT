# GPT-5.6 xhigh independent review — quaternion boundary

- Component: `quaternion-boundary`
- Obligation: `FLT-HIST-QUATERNION`
- Reviewed artifact: `stage-1-opus48-primary.md`
- Agent: `gpt56xhigh-independent-reviewer-d6`
- Backend/model: `codex` / `gpt-5.6-sol`
- Reasoning/transport/sandbox: `xhigh` / `exec` / `read-only`
- Scheduled budget: `1500s`
- Transport result: `SUCCESS`
- Actual elapsed: `279757ms` (`real 279.76s` from `/usr/bin/time`)
- Codex rollout/request correlation: `019f6f11-8b92-7181-84e7-95afd53909ff`
- Codex turn/request correlation: `019f6f11-8efc-79c3-8e23-bd21eb000494`
- Provider-level request IDs: not exposed by the Codex `exec` transport
- Final token count: `1412423` input (`1305856` cached input), `13710` output
  (`8387` reasoning output), `1426133` total
- Verdict: **REVISE**
- Promotion: none; source correction and the mandatory human gate remain open

## Verdict

**REVISE**

## Blocking findings

- Registered evidence cannot establish a page-exact primary source. `SRC-017` and `SRC-022` are
  Voight 2021 secondary results covering only the order-unit terminal; neither supplies the
  adelic-to-order construction or exact-kernel injection.
- Consequently, the T2 requirement that every named assumption be typed, finite, and sourced is
  unmet. The mandatory human gate may be convened, but cannot affirmatively authorize axiom
  registration until that locator is verified.
- The proposed interface is mathematically sound but not strictly minimal: `hUo` is redundant for
  stabilizer finiteness. Compactness supplies the compact projective image and total definiteness
  supplies the required adelic discreteness. The `U = ⊤` example shows that compactness cannot be
  removed, not that openness is necessary.

## Nonblocking findings

- The terminal theorem is credible; no counterexample was found. Opus correctly rejects the
  norm-one injection, central compactness, unconjugated-order, and finite-double-coset shortcuts.
- The exact consumer is correctly identified at
  `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean:496`. The checked
  `QuaternionStabilizerSignatureProbe.lean` elaborates, definitionally supplies `ℒ.Δ D g`, and
  reports exactly `propext`, `Classical.choice`, and `Quot.sound`. A read-only check also confirmed
  that the general `U`-parameterized signature applies once the scalar subgroup is explicit.
- The dependency account needs narrowing: `ΔIndex` and `ΔIndex_mul_relIndex` themselves retain
  standard-trio closure and do not inherit the historical axiom. Actual inheritors include the
  nonzero-index arguments in `InnerProduct.lean` and the sufficiently-small instance in
  `HeckeOperators/Concrete.lean`, followed by the registered
  `FLT-HIST-QUATERNION -> FLT-SUPPORT-AUTOMORPHIC` edge.
- The clean probe is a signature audit with a local hypothesis, not evidence for the mathematical
  theorem or its provenance. At T2, downstream closure would contain the newly authorized named
  axiom plus the standard trio; at T3 that named axiom must disappear.

## Exact next human-gate question

Has a human reviewer verified, from a primary pre-1990 scan, an exact
author/title/year/theorem-or-lemma/printed-page result proving for every totally real `F`, totally
definite `D/F`, compact `U <= GL₂(A_f)`, and arbitrary `g`, that
`(U A_f^x ∩ g^-1 D^x g) / F^x` is finite—including or explicitly implying the adelic-to-order and
exact scalar-kernel bridges—and, if so, is the matching minimal Lean interface, with `hUo` removed
unless the source requires it, authorized as the single named T2 assumption?
