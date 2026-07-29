# Stage 3 — GPT-5.6 xhigh good-reduction build response

## Verdict

`BOUNDED-PREFIX-GREEN`

The unchanged target `WeierstrassCurve.torsion_unramified_of_good_reduction` remains admitted. The
run proved and promoted only the first, reusable part of the existing point-specialization contract:

- `ValuationSubring.baseRingHom`;
- `ValuationSubring.coe_baseRingHom`;
- `ValuationSubring.isLocalHom_baseRingHom`.

Each declaration audits to exactly `[propext, Classical.choice, Quot.sound]`.

## Execution

- builder: `gpt56xhigh-builder`
- model: `gpt-5.6-sol`
- effort: `xhigh`
- session: `019faf76-c0c6-7773-84a6-18d4324af7d8`
- transcript: `/Users/philiphaynes/.codex/sessions/2026/07/30/rollout-2026-07-30T06-00-23-019faf76-c0c6-7773-84a6-18d4324af7d8.jsonl`
- bridge duration: `1,360,063 ms`
- turn duration: `1,358,800 ms`
- input tokens: `11,248,758` including `10,869,760` cached
- output tokens: `36,938`
- reasoning output tokens: `16,703`
- total tokens: `11,285,696`

The initial forced-hash build could not update hash files through read-only dependency-cache
symlinks. The builder copied the exact ignored `.lake` dependencies into this worktree and reran the
same command successfully. No tracked cache artifact changed.

## Validation

- direct elaboration of `GoodReduction.lean`: passed, with only the pre-existing target admission;
- narrow build: passed, 2,505 jobs;
- `lake -H build FLT FLTMethodology`: passed, 9,047 jobs;
- `git diff --check`: passed;
- added-line prohibited-token scan: no match;
- whole target file: exactly one `sorry`, the unchanged target.

The adjacent existing declarations `inertia_smul_residue_eq`, `inertia_residue_smul_eq`, and
`torsion_fixed_of_invariant_injective` also retain exactly the standard trio. The target itself
still audits to the trio plus `sorryAx`.

## Exact remaining boundary

The local base-map, locality, and coefficient-compatibility fields of
`FLTMethodology.GoodReduction.PointSpecializationContract` are discharged. The smallest remaining
provider is its geometric tail:

1. construct reduction from separable-closure elliptic points to the reduced projective curve;
2. prove invariance of that reduction under inertia;
3. prove injectivity on `n`-torsion when `n` is nonzero in the residue field.

Pinned Mathlib reduces Weierstrass coefficients but has no projective-point specialization map,
no non-injective residue map for projective points, no Neron-model bridge, and no elliptic-torsion
finite-etale object that supplies the injectivity theorem. The out-of-tree AINTLIB declarations are
not on the pinned project import path and expose no checked bridge to this Weierstrass statement.

## Promotion boundary

This is a proved prerequisite only. It does not close `torsion_unramified_of_good_reduction`,
`FLT-TATE-UNRAMIFIED`, any Tate/Frey consumer, or FLT, and it authorizes no new axiom.
