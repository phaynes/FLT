# FLT completion multi-model run

Authority: typed work order
`helios-control/work-orders/flt-completion.work-order.ndjson`.

Each component directory records the exact stage prompt and model output. Stage 1 uses three fresh,
independent contexts:

- `stage-1-sonnet5.md`
- `stage-1-fable5.md`
- `stage-1-gpt56xhigh.md`

Produced components then record `stage-2-synthesis-gpt56xhigh.md`,
`stage-3-review-fable5.md`, and later the bounded build and Opus review evidence. Historical
components use the same shape but register an exact named T2 axiom rather than claiming a proof.

The model artifacts are advisory. Lean builds and declaration axiom audits are authoritative. A
component cannot move to `proved` merely because the three designs agree. Fable-bound calls are
serialized across components; Sonnet, GPT, and Opus calls may run concurrently.

## Difficulty-scaled timeout and action-cost contract

New attempts use the work-order difficulty rather than a flat timeout. The exact per-attempt budgets
are:

| Difficulty | Design | Build | Synthesis | Review |
|---|---:|---:|---:|---:|
| 1–3 | 900s | 1200s | 600s | 900s |
| 4–5 | 1500s | 2100s | 1200s | 900s |
| 6–7 | 2400s | 3000s | 1800s | 1500s |
| 8 | 3000s | 3600s | 2100s | 1800s |
| 9–10 | 3600s | 5400s | 2700s | 2100s |

Agreement-gate iterations receive the design budget and are limited to two. A timeout is an
environmental `TIMEOUT / NO VERDICT`: it cannot promote a stage. Exactly one retry is allowed at
1.5 times the scheduled budget, capped at 5400 seconds. A second timeout becomes `NO-RESULT` and the
component moves to an engineering decomposition or budget blocker while other work continues. The
serialized Fable lane receives its full component budget and does not consume the parallel lanes'
budgets.

Every attempt is costed in `methodology/control/flt-completion-attempts.ndjson`: granted budget,
actual wall time, input/cache/output token counters, transport outcome, and content verdict. Rows
created before this operator contract remain labelled `legacy-flat-pre-contract`; successful legacy
attempts are retained, while legacy timeouts remain `NO VERDICT` and are never treated as reviews.

The external task-manager store is not mutated by this run because the standing operator boundary
forbids writes outside this FLT repository. The FLT-owned execution ledger, monitor journal, commits,
and Helios read-only projection record the stage transitions until that boundary is relaxed.
