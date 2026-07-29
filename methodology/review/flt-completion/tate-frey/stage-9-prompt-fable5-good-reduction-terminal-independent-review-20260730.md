# Stage 9 — Fable 5 independent review of good-reduction terminal candidate

Act as an independent mathematical and Lean reviewer. This is a read-only review: do not edit any
file, mutate Helios, or perform git operations. Treat the producer and controller reports as
untrusted claims and reproduce the decisive checks yourself.

## Frozen candidate

- repository root: `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`
- branch: `codex/ca-flt-good-reduction-specialization-20260730`
- base: `f9d2638c16946414af508c71b8d59aedcc9b056f`
- proof candidate: `96c0af95883c372e387181da659df43033804f6d`
- target: `WeierstrassCurve.torsion_unramified_of_good_reduction`
- candidate scope: one prime-to-residue-characteristic good-reduction unramifiedness leaf inside
  `FLT-TATE-FLAT`; not the aggregate obligation and not FLT.

Read completely:

1. `methodology/review/flt-completion/tate-frey/stage-7a-fable5-torsion-injectivity-native-design-response-20260730.md`
2. `methodology/review/flt-completion/tate-frey/stage-7b-gpt56xhigh-torsion-injectivity-literature-design-response-20260730.md`
3. `methodology/review/flt-completion/tate-frey/stage-7c-root-torsion-injectivity-synthesis-and-probe-20260730.md`
4. `methodology/review/flt-completion/tate-frey/stage-8-gpt56xhigh-direct-torsion-injectivity-build-response-20260730.md`
5. the full diff `f9d2638c16946414af508c71b8d59aedcc9b056f..96c0af95883c372e387181da659df43033804f6d`;
6. every changed Lean file and all directly consumed theorem definitions.

## Review duties

1. Verify the terminal statement is unchanged and the proof has no target-equivalent assumption,
   new axiom, admission, hidden characteristic exclusion, completion/Henselian assumption, or
   unjustified coercion.
2. Check the mathematical route, especially:
   - integrality of both affine coordinates;
   - primitive projective-residue coordinate recovery;
   - the actual `ΨSq_ofNat` factor split;
   - separability and pointwise-coprimality use in odd/even and residue-characteristic-two cases;
   - derivation of nonzero `2` only in the even branch;
   - the equal-x negation case and exact two-torsion/self-negation conclusion;
   - point-at-infinity cases;
   - use of `torsion_fixed_of_invariant_injective` and `pointSpecialization_inertia`.
3. Independently run direct elaboration, the narrow build, the 17-declaration axiom audit, added-line
   prohibited-token scan, `git diff --check`, and `lake -H build FLT FLTMethodology`.
4. Distinguish local elaboration from mathematical fidelity. Identify any proof that succeeds only
   because a hypothesis or theorem is stronger than the intended source boundary.
5. Confirm the economic classification: PASS may retire only the named unramifiedness leaf. It may
   not mark `FLT-TATE-FLAT`, any other L0 obligation, any downstream join, or FLT complete.

## Response contract

Return one verdict: `PASS-LEAF`, `REVISE`, or `BLOCK`.

Then report:

- exact findings with file and line references;
- commands, exits, job counts, and complete axiom classification;
- whether every stated edge case is preserved;
- whether the candidate can be promoted as the one named leaf;
- the two still-open `FLT-TATE-FLAT` mathematical inputs;
- confirmation that no file, git, or Helios mutation occurred.

Do not award an aggregate obligation closure merely because all mechanical checks pass.
