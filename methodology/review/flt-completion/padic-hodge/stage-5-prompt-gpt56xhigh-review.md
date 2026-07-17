# Stage 5 prompt — GPT-5.6 xhigh independent p-adic-Hodge review

Difficulty 10. Fresh independent read-only review. Do not edit the repository.

Read:

- `methodology/review/flt-completion/padic-hodge/stage-2-gpt56xhigh-review.md`
- `methodology/review/flt-completion/padic-hodge/stage-3-fable5-diversity.md`
- `methodology/review/flt-completion/padic-hodge/stage-4-opus48-synthesis.md`
- the pinned Lean APIs cited there.

Independently verify the exact proposed `MLTPadicHodgeWeightData` boundary. In temporary probes,
check global embedding indexing, the one-global-`a` interval, `Algebra.IsUnramifiedIn`,
`GaloisRepDual` continuity, the `{-1,0}` at rho / `{0,1}` at the dual convention, and the two
guard lemmas. Confirm that flatness remains on the integral model, crystallinity remains on the
generic fibre, and automorphic unramifiedness at ell remains RACAR-owned.

Return `PASS`, `REVISE`, `UNCERTAIN`, or `REFUTED`. Classify any revision as substantive
mathematical/statement-level versus mechanical/scope-only. State whether any further Fable pass is
required under the typed rule. Give the exact bankable declarations, the open G1/G2/G4/G5/G6/G7
providers, build command, expected axiom surface, and first likely residual Lean goal. A review
verdict cannot promote the obligation; the kernel build and declaration audit remain authoritative.
