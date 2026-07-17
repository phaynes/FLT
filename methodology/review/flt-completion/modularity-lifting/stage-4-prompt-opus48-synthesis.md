# Stage 4 prompt — Opus 4.8 modularity-lifting synthesis

Difficulty 10. Read-only synthesis. Do not edit repository files, task state, graph rows, or Lean
sources. Temporary probes outside the repository are allowed.

Read the complete stage-1 Opus design, stage-2 GPT review, and stage-3 Fable diversity design for
`modularity-lifting`, plus the current coefficient and p-adic-Hodge reviewed artifacts.

Synthesize one exact design for `FLT-MLT-SOURCE` and `FLT-SGOOD-SELECTED` that:

- freezes the five standard-trio-clean boundary units from the Fable pass;
- preserves repository/source separation;
- carries one coefficient owner across residual agreement and cyclotomic irreducibility;
- keeps generic-fibre tame quotient, integral flat descent, and trace-on-J as distinct boundaries;
- assigns cyclotomic degree, complex embedding, support-away-ell, p-adic-Hodge, and RACAR ownership
  explicitly;
- does not import or rely on the sorried `cyclic_base_change` in any declaration claimed clean;
- states the smallest first buildable `SelectedGoodRepositoryBoundary` probe exactly.

Adjudicate every disagreement explicitly. Return `READY-FOR-GPT-REVIEW`, `OBSTRUCTION`, or
`NO-RESULT`, with exact Lean signatures, dependency order, source/consumer ledger, counterexamples,
stop-losses, and the first expected residual Lean goal. No promotion is authorized.
