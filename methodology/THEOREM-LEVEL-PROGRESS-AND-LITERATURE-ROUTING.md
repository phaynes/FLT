# Theorem-level progress, literature routing, and resource policy

Task: `task:ca-flt-theorem-progress-literature-routing-20260719`

## Purpose

The 55 proof obligations are programme milestones, not theorem counts. They remain useful for
dependency and governance reporting, but they are too coarse to estimate proof completion. The
authoritative fine-grained input is `methodology/control/theorem-contracts.ndjson`.

The migration is deliberately coverage-aware. A theorem ratio applies only to inventoried
obligations, and the cockpit must display `obligations_inventoried / obligations_total` beside it.
No partial inventory may be labelled whole-programme completion.

## Counting rules

Each required mathematical contract has one stable `theorem_id`. A record says whether it is a
target, helper, definition, or conditional wrapper. Only records with
`required_for_completion: true` enter the theorem denominator.

A theorem is kernel-clean only when `proof_status` is `kernel-clean`, `reviewed`, or `integrated`.
An axiom-clean conditional proof remains `conditional` while a premise is open. Definitions of
open propositions are `stated`, not proved. Independent review and integration are reported as
separate numerators.

Adding helper lemmas cannot silently improve the completion ratio: new required contracts change
the denominator and remain visible in history; non-required exploratory helpers are reported but
excluded.

## Fine-grained literature routing

Literature is allocated per theorem contract rather than per component. Every required source
entry carries:

- the source-register ID;
- an exact theorem/page/section locator where known;
- whether that locator has been verified;
- the role of the source for this theorem;
- the Lean-hypothesis translation state; and
- the exact residual mathematical or formal gap.

When `literature_required` is true and `literature_status` is neither `exact` nor `verified`, the
Rust scheduler routes the contract to `literature-lookup`. Proof design and proof dispatch are not
eligible until the source and hypothesis translation are ready. A component citation inherited
from a blueprint is not an exact theorem source.

The theorem action emitted to the design/proof lane contains these literature fields. The review
package must retain the same crosswalk, the final Lean statement, the axiom audit, build evidence,
candidate SHA, and the human-readable proof.

## Easy-first policy

The scheduler considers only open contracts whose theorem dependencies are kernel-clean. It then
orders useful work deterministically by:

1. lowest implementation difficulty;
2. lowest estimated token cost;
3. greatest number of downstream contracts unlocked;
4. critical-path position; and
5. stable theorem ID.

This is dependency-ready useful easy-first, not indiscriminate short-proof harvesting. A simple
off-path lemma does not displace a similarly cheap theorem that unlocks the FLT closure.

Resource recommendations are recorded per theorem:

| Difficulty | Default approach | AI intensity |
|---|---|---|
| 1–3 | direct Lean assembly, simplification, build and axiom audit | none or low |
| 4–6 | one coding/proof model with Lean tooling; independent standard review | low |
| 7–8 | exact literature brief, one bounded design, specialist proof model | medium |
| 9–10 | source/definition programme, specialist design, independent mathematical review | high |

The recorded route may be tightened for a particular theorem. Expensive diversity or multi-model
design is not the default for routine Lean closure.

## Current migration state

The first ledger covers the active `FLT-TAME-RESIDUE`, `FLT-CLASS-FIELD`, `FLT-TATE-FLAT`, and
`FLT-TATE-UNRAMIFIED` tranches. It does not claim a global theorem total. Each remaining obligation
must undergo the same contract decomposition before whole-programme theorem completion can be
estimated honestly.
