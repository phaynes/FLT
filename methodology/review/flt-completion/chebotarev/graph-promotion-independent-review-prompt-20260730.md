# Independent graph-promotion review — FLT Chebotarev adapter

Act as an independent read-only control, mathematical, and evidence reviewer. Do not edit files,
commit, or change Helios task state. Do not claim `FLT-CHEBOTAREV` or FLT complete.

Repository:
`/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730`

Graph/evidence candidate: `b5e950f5fecfc7b61ec2444c47115ed65e407866`

Reviewed implementation candidate: `ee0f49e`

Later HEAD may differ only by this prompt. Verify that, then inspect the complete candidate diff.

Required read-only checks:

- `git status --short`, ancestry, intervening paths, and `git diff --check`;
- parse every line of the five NDJSON control files changed by the candidate;
- independently verify 56 unique obligations, 103 unique edges, all edge endpoints present, and no
  dependency cycle;
- verify `methodology/spec/flt-proof-program.instances.json` contains the same obligation and edge
  sets as the canonical NDJSON;
- verify the attempt telemetry reconciles exact model, effort, elapsed-time, token, transport, and
  verdict data with the retained transcripts;
- inspect the exact Fable 5 executable `PASS`, both GPT `REVISE` reviews, build evidence, source
  packet, and actual Lean declarations.

Adjudicate the semantic split:

1. `FLT-CHEBOTAREV-DENSITY` must own only the unwitnessed proposition
   `RatArithmeticFrobeniusConjugacyDensity`, remain `absent`, and have no hidden witness or
   authorized T2 assumption.
2. `FLT-CHEBOTAREV` must remain `definition-gap`, despite the deterministic adapter being
   kernel-clean and independently reviewed, because density and fixed-coefficient family wiring
   remain open.
3. The new dependency edge must point from density to comparison; existing compatible-family
   consumers must continue to depend on `FLT-CHEBOTAREV`.
4. No status, estimate, source reference, completion gate, or telemetry row may launder a conditional
   theorem, plan-only review, read-only build failure, or secondary literature into closure.
5. The Fable `PASS` may approve the deterministic adapter only. It must not approve density,
   historical-assumption authorization, the family consumer, or FLT.

Return exactly one leading verdict: `PASS`, `REVISE`, or `NO-RESULT`, followed by executed checks,
findings ordered by severity, exact approved state transitions, and exact remaining open boundaries.
