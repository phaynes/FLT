# FLT reviewer-capacity fallback

## Purpose

Keep bounded proof work moving when Claude capacity is temporarily unavailable without representing
a second GPT-5.6 instance as model-diverse assurance. Lean's kernel remains the proof checker; model
review assesses statement fidelity, source use, scope, dependencies, and control-plane honesty.

## Ordered ladder

1. Assign independent review to Fable.
2. If Fable is unavailable because of capacity, service, or timeout, record the failed attempt and
   assign Claude Opus 4.8.
3. If both Claude profiles are unavailable for the same operational reasons, assign
   `gpt56xhigh-capacity-fallback-reviewer` in a new session and a clean review worktree frozen at the
   candidate commit.
4. Do not silently switch providers or reuse the builder session.

Unavailability means a provider or capacity failure, not an adverse mathematical verdict. `REVISE`,
`UNCERTAIN`, and `REFUTED` must be handled as review outcomes and may not trigger a more agreeable
reviewer.

## Independence controls for the GPT fallback

The controller must provide a compact evidence manifest rather than the producer conversation:

- immutable candidate commit SHA and clean review-worktree path;
- exact theorem declarations and theorem-contract records in scope;
- exact primary-source files, hashes, and page/theorem locators;
- expected target-stage axiom policy;
- targeted and umbrella build commands;
- exact `#print axioms` commands; and
- the acceptance criteria and explicit non-closure boundary.

The reviewer must start with `session_strategy = "fresh"`, inspect the candidate independently,
re-run the commands, and record HEAD and tracked status before and after. It may populate ignored
build caches but must not modify tracked files. A review is invalid if the candidate SHA moves, the
worktree was dirty, the commands did not run, or the transcript/identity/evidence record is absent.

## Verdict and promotion semantics

`PASS-SAME-FAMILY` is an honest, weaker assurance grade. It may advance a bounded implementation
when all of the following hold:

- the theorem statement and source boundary are unchanged;
- no custom axiom or assumption was added;
- fresh targeted and required umbrella builds pass;
- exact declaration axiom audits satisfy the target-stage policy; and
- the control artefacts do not claim closure beyond the audited declarations.

It is not model-diverse review. A source reinterpretation, theorem-statement change, new assumption,
target-stage policy change, or difficulty-9/10 promotion remains provisionally reviewed and must
retain an explicit Fable/Opus diversity-review debt before final integration or terminal programme
closure. Later diversity review inspects the same frozen SHA; it does not erase the GPT review trace.

## Capacity-safe review prompt

Use the prompt embedded in `gpt56xhigh-capacity-fallback-reviewer`. The controller briefing must end
with this candidate-specific block:

```text
FROZEN CANDIDATE
- repository/worktree: <absolute clean review path>
- commit: <immutable SHA>
- declarations: <exact Lean names>
- contracts: <exact theorem-contract lines>
- literature: <source IDs, local paths or URLs, SHA-256, exact locators>
- axiom policy: <allowed closure>
- targeted build: <command>
- umbrella build: <command>
- axiom audits: <commands>
- acceptance: <bounded criteria>
- non-closure: <what this candidate does not establish>

Do not read or request the producer transcript. Verify this material independently and return the
required verdict plus command output summaries, tracked-status comparison, defects, and residuals.
```

## Overnight stop rules

The fallback does not make an unbounded proof loop safe. An unattended controller must stop after
one failed build-repair cycle, any statement/source/axiom-policy change, a dirty tracked worktree, a
moved candidate SHA, missing literature evidence, reviewer uncertainty, or exhausted time/token
budget. It checkpoints the attempt and leaves the task visible rather than manufacturing completion.
