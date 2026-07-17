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

The external task-manager store is not mutated by this run because the standing operator boundary
forbids writes outside this FLT repository. The FLT-owned execution ledger, monitor journal, commits,
and Helios read-only projection record the stage transitions until that boundary is relaxed.
