# Stage 1 non-Fable attempt record — Tate–Frey remaining cluster

Component: `tate-frey`  
Obligations: `FLT-TATE-FLAT`, `FLT-TATE-UNRAMIFIED`, `FLT-TATE-WEIL`, `FLT-SUPPORT-TATE`, and
`FLT-FREY-HR`  
Regression-only obligations preserved: `FLT-TATE-TORSION`, `FLT-TORSION-001`  
Work-order difficulty: `8/10`  
Scheduled design budget under the difficulty contract: `3000 s`  
Final status of this lane: `CANCELLED / SUPERSEDED / NO VERDICT`

The operator's producer ladder superseded the original tri-design producer assignments before any
Sonnet or GPT design completed. No partial stream was retained or promoted. Opus 4.8 is now the
primary design/build model; GPT-5.6 xhigh is the independent reviewer. This file is environment and
cost evidence only and does not advance the component's review, DoR, or proof state. The two closed
torsion/Galois obligations remain regressions and were never reopened by this lane.

| Attempt | Model / transport | Configured budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| selector check | `claude-sonnet-5-0` / Claude CLI | old default | `< 1 s` | unavailable | `ENVIRONMENT ERROR / NO VERDICT`: invalid model selector; corrected to `claude-sonnet-5` |
| old flat-budget run | `claude-sonnet-5` / Claude CLI | `600 s` | `600 s` | unavailable | `TIMEOUT / NO VERDICT` |
| old flat-budget run | `gpt-5.6-sol`, xhigh / Codex direct exec | `600 s` | `600 s` | unavailable | `TIMEOUT / NO VERDICT` |
| interim flat-budget run | Sonnet + GPT independently | `1800 s` | not emitted; `< 1800 s` | unavailable | cancelled when the difficulty-scaled timeout contract superseded the flat cap; no output |
| in-memory all-difficulty launch | Sonnet + GPT independently | `3600 s` | `< 5 s` | unavailable | cancelled because Tate–Frey must use its exact d8 tier; no output |
| exact d8 tier | `sonnet5-designer-d8` / Claude CLI | `3000 s` | `448 s` at cancellation sampling | unavailable | `CANCELLED / SUPERSEDED / NO VERDICT`, exit `130` |
| exact d8 tier | `gpt56xhigh-designer-d8` / Codex direct exec | `3000 s` | `448 s` at cancellation sampling | unavailable | `CANCELLED / SUPERSEDED / NO VERDICT`, exit `130` |

`kg-model-bridge` exposes model, backend, duration, exit code, and output character count only in a
completed `TeamResult`; it does not expose provider token counts in its result schema. Timeout and
interrupted attempts produced no `TeamResult`, so exact token use is unavailable rather than
estimated.

The full independent-design prompt remains in `stage-1-prompt-non-fable.md` as advisory planning
evidence. There is no `stage-1-sonnet5.md` or `stage-1-gpt56xhigh.md` result from this lane.

## Opus-first primary producer

The superseding producer ladder completed a fresh read-only Opus 4.8 primary design under the exact
d8 budget. This does not itself advance the central control plane; it is ready for the separately
governed GPT independent-review stage.

| Attempt | Agent / model / transport | Budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| primary design | `opus48-primary-designer-d8` / `claude-opus-4-8` / Claude CLI | `3000 s` | `669.147 s` | `55,078` input; `281,398` cache-create; `2,394,660` cache-read; `37,978` output; `2,769,114` total including cache, deduplicated over `46` request IDs | `READY-FOR-GPT-REVIEW` |

Full evidence: `stage-1-opus48-primary.md`. Claude session:
`89186f12-5a49-417d-bef5-e7e0e9c682cb`.

## GPT-5.6 xhigh independent review

| Attempt | Agent / model / transport | Budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| independent review | `gpt56xhigh-independent-reviewer-d8` / `gpt-5.6-sol`, xhigh / Codex direct exec | `1800 s` | `467.232 s` | `4,393,053` input; `4,171,008` cached input; `22,099` output (`15,387` reasoning); `4,415,152` total | `REVISE`; Fable diversity trigger `YES` |

Full evidence: `stage-2-gpt56xhigh-review.md`. Codex session:
`019f6f0c-0fbb-7020-aa76-0a3db9e575d4`.
