# Stage 6 — Fable 5 independent point-specialization review

## Verdict

`PASS-KERNEL-GREEN-PREFIX`

Fable independently reviewed the frozen Stage 5 source diff and the pinned Mathlib declarations.
It found no mathematical, representative-independence, model-compatibility, characteristic, build,
or axiom defect in the point-specialization and inertia-invariance prefix.

The pass authorizes only the new prerequisite declarations. It does **not** authorize torsion
injectivity, `WeierstrassCurve.torsion_unramified_of_good_reduction`, `FLT-TATE-UNRAMIFIED`, a
downstream consumer, an assumption, or FLT.

## Frozen evidence

- candidate source commit: `9573e69`
- diff base: `35bf790`
- review-prompt commit and reviewed worktree head: `75d8ef8`
- task: `task:ca-flt-good-reduction-specialization-20260730`
- owning obligation: `FLT-TATE-UNRAMIFIED`
- reviewer: `fable5-designer-d8`
- model: `claude-fable-5`
- Claude session: `6cb0e3ca-2456-45f7-aec7-ab0d69916ccc`
- transcript:
  `/Users/philiphaynes/.claude/projects/-Volumes-second-store-devel-proof-forks-FLT-good-reduction-specialization-20260730/6cb0e3ca-2456-45f7-aec7-ab0d69916ccc.jsonl`
- model duration: `1,119,423 ms`
- requests: `76`
- input tokens: `1,224`
- cache-creation input tokens: `391,241`
- cache-read input tokens: `6,510,459`
- output tokens: `213,703`

## Independent findings

The reviewer checked the following against the actual source and pinned library rather than the
producer report:

1. `exists_unitCoordinateNormalization` uses the correct order convention for a valuation subring
   and is valid for arbitrary valuation subrings, not only discrete rank-one valuations.
2. Primitive integral representatives that differ by a field scalar differ by a unit. Consequently
   residue projective classes are independent of the chosen normalization, including the zero
   quotient class and the quotient orientation.
3. The nonsingularity bridge is valid at infinity and in characteristics two and three.
4. The extended integral model reduces to the exact target curve by equality, not merely by an
   unbridged isomorphism; the local-map and scalar-tower uses match the target.
5. `projectiveResidue_inertia` remains valid despite noncomputable normalization because the residue
   class is independent of that choice.
6. `pointSpecialization` is total on the exact source point type and
   `pointSpecialization_inertia` has the exact invariant shape consumed by
   `torsion_fixed_of_invariant_injective`.
7. The new declarations have only `[propext, Classical.choice, Quot.sound]`; the unchanged target
   still adds `sorryAx`.
8. The exact remaining mathematical boundary is

   ```lean
   Set.InjOn (A.pointSpecialization R k E hA)
     (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))
   ```

   under `NeZero (n : IsLocalRing.ResidueField R)`.

## Executable evidence and caveat

Fable independently passed direct elaboration of `GoodReduction.lean`, direct elaboration of the
methodology probe, from-source re-elaboration with appended declaration-level axiom audits, and
changed-line prohibited-token and attribute scans. Its read-only plan mode prevented the two forced
packaging builds from running inside the review session. The controller had already independently
run and passed the forced narrow build (`2505` jobs) and forced umbrella build (`9047` jobs) at the
frozen candidate, so this is an operational limitation of the reviewer session rather than a missing
controller gate.

Fable also found one cosmetic `git diff --check` issue: a blank line at the end of the Stage 5
Markdown report. The controller removed that blank line after review; no Lean source was affected.

## Promotion boundary

The point-specialization and inertia-invariance prefix is independently reviewed and kernel-green.
The Helios task remains executing because its requested good-reduction torsion theorem is not yet
proved. No obligation or graph node is promoted by this review alone.
