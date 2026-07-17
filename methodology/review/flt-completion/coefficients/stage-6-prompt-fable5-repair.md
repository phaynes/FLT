# Stage 6 prompt — Fable 5 coefficient-boundary repair

Difficulty 10. Read-only design pass. Do not edit the repository, task state, graph, or Lean sources.
Use temporary Lean probes outside the repository only.

Read:

- `methodology/review/flt-completion/coefficients/stage-3-fable5-diversity.md`
- `methodology/review/flt-completion/coefficients/stage-4-opus48-synthesis.md`
- `methodology/review/flt-completion/coefficients/stage-5-gpt56xhigh-review.md`
- the exact live consumers named by Stage 5.

Repair only the substantive delta identified by the fresh independent review:

1. retain or explicitly replace the generic-closure embedding/tower needed by
   `cyclic_base_change` and `mem_isCompatible`;
2. generalize all module universes in `GroupContract`;
3. retain `CoefficientData extends StableLatticeData`;
4. name the missing residue `IsLocalHom` / completeness adapter without pretending it is proved;
5. preserve the same-`O` two-lattice charpoly argument and keep cross-`O` comparison open;
6. produce the exact smallest `MLTCoefficientData` probe signatures and a correct live-consumer
   ledger.

Re-run temporary elaboration and `#print axioms` checks for every proposed bankable declaration.
Require exactly `[propext, Classical.choice, Quot.sound]`. Return exactly one of
`DESIGN-VIABLE`, `OBSTRUCTION`, or `NO-RESULT`, followed by the repaired signatures,
dependency order, probe evidence, still-open mathematical providers, and the first residual Lean
goal. Do not promote `FLT-MLT-COEFFICIENTS`.
