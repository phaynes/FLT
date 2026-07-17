# GPT-5.6 xhigh auxiliary/residual-image review telemetry

- Component: `auxiliary-residual-image`
- Obligations: `FLT-AUX-CURVE`, `FLT-AUX-LOCAL-FIELD`, `FLT-RESIDUAL-IMAGE`
- Agent/model: `gpt56xhigh` / `gpt-5.6-sol`
- Backend: Codex CLI, read-only sandbox
- Session: `019f7041-45c8-79b3-b32b-e878d2983968`
- Scheduled review budget: 2100 seconds
- Actual elapsed: approximately 1176 seconds (filesystem envelope 23:25:53–23:45:29 AEST)
- Transport outcome: `SUCCESS`
- Content verdict: `REVISE-SUBSTANTIVE`
- Typed Fable decision: `KEEP` — difficulty 10 is above 7 and the review found mathematical and
  statement-level defects in absolute irreducibility, unramifiedness, disjointness orientation,
  source ownership, and graph factorisation.
- Promotion allowed: no
- Token usage: 12,579,982 input tokens including 12,162,560 cached input tokens; 53,338 output
  tokens including 31,494 reasoning tokens; one request.
- Final reviewed HEAD: `fee713968dafb64725ff653136fad7443a40603e`
- Evidence: `stage-2-gpt56xhigh-review.md`

The repository moved during the review only through controller status commits. The reviewer checked
the delta and confirmed that no relevant Lean, source, or graph content changed. Temporary Lean
probes elaborated the accepted boundary signatures with exactly `propext`, `Classical.choice`, and
`Quot.sound`; no repository content was promoted by the review.
