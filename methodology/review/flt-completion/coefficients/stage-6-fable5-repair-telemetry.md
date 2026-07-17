# Fable 5 coefficient-repair transport telemetry

Component: `coefficients / FLT-MLT-COEFFICIENTS`
Initial outcome: **RESOURCE LIMIT — NO VERDICT**
Agent: `fable5-designer-d10`
Model/backend: `claude-fable-5` / Claude Code
Scheduled timeout: 3600 seconds
Exit code: 1
Token usage: unavailable; provider rejected the session before a completion envelope
Retry: completed after the provider reset at 00:50 Australia/Sydney

Provider error:

```text
You've hit your session limit · resets 12:50am (Australia/Sydney)
```

The initial failure was an environment/resource outcome, not a content verdict, and did not promote
the stage. The authorized retry below supplies the required typed Fable result.

## Authorized retry

- Outcome: **SUCCESS — DESIGN-VIABLE**
- Bridge session: `51067`
- Budget: 3600 seconds
- Actual elapsed: 1802187 ms
- Exit code: 0
- Token usage: unavailable from the bridge completion envelope
- Evidence: `stage-6-fable5-repair.md`

The retry discharged the closure-descent design boundary with trio-clean temporary proofs and
isolated the remaining provider graph. It did not edit Lean source or promote the obligation.
