# Stage 8 — GPT-5.6 xhigh direct torsion-injectivity build response

## Classification

The producer returned `CLOSED` for the unchanged theorem
`WeierstrassCurve.torsion_unramified_of_good_reduction`. This is a candidate closure of the
prime-to-residue-characteristic good-reduction unramifiedness leaf inside `FLT-TATE-FLAT`.
It is not independent review, does not close the other `FLT-TATE-FLAT` leaves, and does not close
the aggregate L0 obligation.

## Immutable boundary

- base: `f9d2638c16946414af508c71b8d59aedcc9b056f`
- candidate: `96c0af95883c372e387181da659df43033804f6d`
- branch: `codex/ca-flt-good-reduction-specialization-20260730`
- producer: `gpt-5.6-sol`, reasoning effort `xhigh`
- Codex session: `019fafff-d4d9-7051-8664-bd0bacc3565f`
- durable local transcript:
  `/Users/philiphaynes/.codex/sessions/2026/07/30/rollout-2026-07-30T08-30-06-019fafff-d4d9-7051-8664-bd0bacc3565f.jsonl`

## Result

The candidate adds an acyclic generic root-separation module and proves the specialization-facing
coordinate, torsion-root, x-separation, zero/affine, and full `Set.InjOn` lemmas needed by the
reviewed inertia assembly. The original terminal theorem statement is byte-identical to its base
statement; only the final `sorry` proof was replaced.

Changed sources:

- `FLT/EllipticCurve/TorsionProof/RootSeparation.lean`: new, 151 lines;
- `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`: `+473/-1`;
- combined: `+624/-1`.

## Producer telemetry

- elapsed: `1,337,223 ms` bridge trace; Codex task duration `1,336,123 ms`;
- input tokens: `9,147,738`;
- cached input tokens: `8,900,608` (included in input);
- output tokens: `43,459`;
- reasoning output tokens: `17,982` (included in output);
- total tokens: `9,191,197`;
- request count: `1`.

## Producer and controller verification

Both the producer and controller independently replayed:

- direct elaboration of both changed Lean files: exit `0`;
- `lake build FLT.KnownIn1980s.EllipticCurves.GoodReduction`: exit `0`, 8,742 jobs;
- `lake -H build FLT FLTMethodology`: exit `0`, 9,048 jobs;
- `git diff --check`: exit `0`;
- unchanged target-statement comparison: exit `0`;
- added-line prohibited-token scan: no matches.

The controller replayed `#print axioms` for sixteen new declarations and the unchanged terminal.
Every declaration reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only changed-source warning is that the preserved target parameter
`[IsSepClosure k ksep]` is now unused. Existing repository and vendor linter warnings were replayed
by the umbrella build.

## Economic and graph effect

Before independent review and integration, earned closure remains zero. If review passes, the
candidate retires one named mathematical leaf of `FLT-TATE-FLAT`: good-reduction
prime-to-residue-characteristic torsion unramifiedness. The aggregate L0 count remains `8/16`
because the universal resultant identity and the finite-flat Hopf/group-scheme provider remain
open. Historical attempt rows that assigned this theorem to `FLT-TATE-UNRAMIFIED` are
classification defects; that aggregate concerns Tate-curve/bad-reduction support.

## Promotion boundary

No programme, aggregate obligation, downstream consumer, or FLT promotion is authorized by this
producer result. The next gate is independent Fable review of candidate
`96c0af95883c372e387181da659df43033804f6d`, followed by controller reconciliation and clean
baseline integration.
