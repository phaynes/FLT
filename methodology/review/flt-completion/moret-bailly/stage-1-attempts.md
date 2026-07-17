# Stage 1 non-Fable attempt record — Moret–Bailly

Component: `moret-bailly`  
Obligation: `FLT-MORET-BAILLY`  
Work-order difficulty: `10/10`  
Scheduled design budget under the difficulty contract: `3600 s`  
Final status of this lane: `CANCELLED / SUPERSEDED / NO VERDICT`

The operator's producer ladder superseded the original tri-design producer assignments before any
Sonnet or GPT design completed. No partial stream was retained or promoted. Opus 4.8 is now the
primary design/build model; GPT-5.6 xhigh is the independent reviewer. This file is environment and
cost evidence only and does not advance the component's review, DoR, or proof state.

| Attempt | Model / transport | Configured budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| selector check | `claude-sonnet-5-0` / Claude CLI | old default | `< 1 s` | unavailable | `ENVIRONMENT ERROR / NO VERDICT`: invalid model selector; corrected to `claude-sonnet-5` |
| old flat-budget run | `claude-sonnet-5` / Claude CLI | `600 s` | `600 s` | unavailable | `TIMEOUT / NO VERDICT` |
| old flat-budget run | `gpt-5.6-sol`, xhigh / Codex direct exec | `600 s` | `600 s` | unavailable | `TIMEOUT / NO VERDICT` |
| interim flat-budget run | Sonnet + GPT independently | `1800 s` | not emitted; `< 1800 s` | unavailable | cancelled when the difficulty-scaled timeout contract superseded the flat cap; no output |
| in-memory all-difficulty launch | Sonnet + GPT independently | `3600 s` | `< 5 s` | unavailable | cancelled when exact tiered agent names became authoritative; no output |
| exact d10 tier | `sonnet5-designer-d10` / Claude CLI | `3600 s` | `448 s` at cancellation sampling | unavailable | `CANCELLED / SUPERSEDED / NO VERDICT`, exit `130` |
| exact d10 tier | `gpt56xhigh-designer-d10` / Codex direct exec | `3600 s` | `448 s` at cancellation sampling | unavailable | `CANCELLED / SUPERSEDED / NO VERDICT`, exit `130` |

`kg-model-bridge` exposes model, backend, duration, exit code, and output character count only in a
completed `TeamResult`; it does not expose provider token counts in its result schema. Timeout and
interrupted attempts produced no `TeamResult`, so exact token use is unavailable rather than
estimated.

The full independent-design prompt remains in `stage-1-prompt-non-fable.md` as advisory planning
evidence. There is no `stage-1-sonnet5.md` or `stage-1-gpt56xhigh.md` result from this lane.

## Opus-first primary producer

The superseding producer ladder completed a fresh read-only Opus 4.8 primary design under the exact
d10 budget. The result is advisory until the separately governed GPT independent review; this lane
does not itself update the central control plane.

| Attempt | Agent / model / transport | Budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| primary design | `opus48-primary-designer-d10` / `claude-opus-4-8` / Claude CLI | `3600 s` | `790.798 s` | `21,748` input; `200,841` cache-create; `1,299,879` cache-read; `35,051` output; `1,557,519` total including cache, deduplicated over `45` request IDs | `UNCERTAIN` |

Full evidence: `stage-1-opus48-primary.md`. Claude session:
`8693c526-59f4-41dc-9450-8fd4c8e272b1`.

## Fable 5 conditional diversity design

| Attempt | Agent / model / transport | Budget | Actual elapsed | Token telemetry | Outcome |
|---|---|---:|---:|---|---|
| alternative design 1 | `fable5-designer-d10` / `claude-fable-5` / Claude CLI | `3600 s` | unavailable; interrupted before completion envelope | unavailable; no completion envelope | `CANCELLED / NO VERDICT`; superseded by the explicit attempt-2 restart at commit `67b0a1d` |
