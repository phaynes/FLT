# FLT completion multi-model run

Authority: typed work order
`helios-control/work-orders/flt-completion.work-order.ndjson`.

Each component directory records the exact stage prompt and model output. The current operator
assignment is an Opus-first producer ladder:

1. Opus 4.8 produces the primary design at the component's difficulty-scaled design budget.
2. GPT-5.6 xhigh independently reviews the design.
3. If that review is clean, Opus 4.8 performs the bounded Lean build at the scaled build budget.
4. The Lean kernel build and exact declaration axiom audit decide the build gate; GPT-5.6 xhigh
   reviews source faithfulness and scope independently.
5. Fable 5 is a conditional alternative design only when both typed conditions hold: the scheduled
   difficulty is greater than Opus's comfort ceiling of 7, and the mandatory GPT review returns a
   substantive mathematical or statement-level `REVISE`. Mechanical, scope, or import-only repairs
   do not trigger Fable.

If the Opus path is clean and kernel-accepted, no Fable diversity pass is run. Below difficulty 8,
Fable is not spent. If Fable is unavailable or exhausts its single retry, Opus may supply the
alternative pass but the collapsed model diversity is flagged for extra human scrutiny. Named T2
axiomatisations and the terminal theorem audit always retain an explicit human agreement gate.

The earlier three-design prompt and output files are retained as superseded advisory evidence; they
cannot promote a stage under this ladder.

The model artifacts are advisory. Lean builds and declaration axiom audits are authoritative. A
component cannot move to `proved` merely because a model reports success. Conditional Fable calls
remain serialized across components and are ordered by critical-path value, then difficulty.
Independent Opus producers may run concurrently across every prompt-ready component. The GPT-5.6
xhigh independent-review lane remains single and serialized; it may not be widened with a
same-family substitute. Skipping Fable never skips this mandatory independent review.

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
