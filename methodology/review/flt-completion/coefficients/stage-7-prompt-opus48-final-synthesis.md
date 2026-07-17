OPUS 4.8 FINAL REPAIR SYNTHESIS — COEFFICIENTS

Act as the non-scarce synthesis producer for `FLT-MLT-COEFFICIENTS` at difficulty 10. Work read-only.
This is the final bounded synthesis after a substantive GPT review and the authorized Fable repair.

Read:

- `methodology/review/flt-completion/coefficients/stage-4-opus48-synthesis.md`
- `methodology/review/flt-completion/coefficients/stage-5-gpt56xhigh-review.md`
- `methodology/review/flt-completion/coefficients/stage-6-fable5-repair.md`
- `FLTMethodology/Probes/MLTSourceBoundary.lean`
- `FLTMethodology/Probes/BrauerNesbittBoundary.lean`
- the exact coefficient, residual, topology, tensor/base-change, and live consumer APIs.

Synthesize one Lean-exact design that resolves all six Stage-5 defects. Independently replay the
Fable temporary signatures and proofs where needed. In particular preserve:

1. the explicit `GenericClosureTower` boundary and the proved closure-descent chain;
2. universe-polymorphic residual models and `GroupContract` use;
3. `CoefficientData extends StableLatticeData`;
4. an explicit, still-open residue `IsLocalHom`/coefficient-glue provider rather than instance
   synthesis;
5. the proved same-coefficient-ring two-lattice characteristic-polynomial path, with cross-ring
   comparison left explicit;
6. the corrected live-consumer and axiom ledger.

Return exact production signatures in dependency order, distinguish proved wiring from the six open
providers T-A1, T-A2, T-A3, M4, BN, and T-IND-CLOSURE, and state the smallest safe production slice.
Run temporary Lean elaboration and `#print axioms` checks outside the repository. The only acceptable
closure for bankable declarations is `[propext, Classical.choice, Quot.sound]`.

Verdict exactly one of `READY-FOR-GPT-REVIEW`, `REVISE`, or `OBSTRUCTION`.

Do not edit repository files, register an axiom, persist a probe, or promote an obligation.
