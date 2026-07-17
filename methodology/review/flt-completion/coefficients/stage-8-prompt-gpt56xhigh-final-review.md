GPT-5.6 XHIGH INDEPENDENT FINAL DESIGN REVIEW — COEFFICIENTS

Act as the independent cross-family reviewer for `FLT-MLT-COEFFICIENTS` at difficulty 10. Work
read-only. Review the final Opus synthesis against the prior substantive review and Fable repair.

Read:

- `methodology/review/flt-completion/coefficients/stage-5-gpt56xhigh-review.md`
- `methodology/review/flt-completion/coefficients/stage-6-fable5-repair.md`
- `methodology/review/flt-completion/coefficients/stage-7-opus48-final-synthesis.md`
- `FLTMethodology/Probes/MLTSourceBoundary.lean`
- `FLTMethodology/Probes/BrauerNesbittBoundary.lean`
- every live consumer and API cited by the synthesis.

Independently determine whether all six Stage-5 defects are actually repaired. Re-run the exact
temporary declarations and proofs outside the repository where necessary; Opus did not rerun them.
In particular test:

1. generalized universes and `CoefficientData extends StableLatticeData`;
2. `GenericClosureTower`, both base-change/conjugation lemmas, and `exists_closure_descent`;
3. the same-`O` two-lattice charpoly and residual-model comparison;
4. explicit residue `IsLocalHom`/coefficient-glue boundaries;
5. the full live-consumer and current axiom ledger;
6. the alleged remaining collapse from `rho.baseChange (AlgebraicClosure ℚ_[p])` back to a consumer
   representation already over that closure. Decide whether this is bankable wiring, an open provider,
   or a statement-level defect in the proposed slice.

Hostile requirements:

- do not accept Stage-6 probe claims without replaying the load-bearing declarations;
- do not permit a hidden universe collapse, closure identification, or cross-coefficient comparison;
- distinguish trio-clean conditional wiring from discharge of T-A1, T-A2, T-A3, M4, BN, and
  T-IND-CLOSURE;
- no `sorryAx`, custom axiom, `knownin1980s`, `admit`, `unsafe`, or `native_decide` may enter a
  bankable declaration;
- no obligation promotion merely because the interface slice is safe to build.

Return exactly one verdict: `PASS`, `REVISE-MECHANICAL`, `REVISE-SUBSTANTIVE`, or `OBSTRUCTION`.
If PASS, give the exact production slice and first residual Lean goal. If REVISE, give exact defects
and whether the bounded two-iteration agreement gate now requires human adjudication.
