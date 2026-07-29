# Stage 6 — Fable 5 independent point-specialization prefix review

Perform an independent, read-only mathematical and executable review of the Stage 5 prefix.

## Frozen evidence

- repository: `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`
- branch: `codex/ca-flt-good-reduction-specialization-20260730`
- candidate commit: `9573e69`
- candidate diff base: `35bf790`
- task: `task:ca-flt-good-reduction-specialization-20260730`
- owning obligation: `FLT-TATE-UNRAMIFIED`

Read the Stage 3 response, Stage 4 Opus design response, Stage 5 prompt and response, the changed
`GoodReduction.lean`, and the actual pinned Mathlib declarations used by the proof. Inspect the real
git diff. Do not rely on the producer's prose or reported builds.

## Review questions

1. Is `exists_unitCoordinateNormalization` mathematically correct for every valuation subring of a
   field, including its choice of maximal multiplicative valuation and its proof of a unit
   coordinate?
2. Do `exists_unit_smul_eq_of_scaled`, `residue_pointClass_eq_of_scaled`, and
   `projectiveResidue` genuinely establish representative independence, or do they hide a zero,
   nonunit, direction-of-scaling, or quotient-orientation defect?
3. Are `nonsingular_of_equation_of_ne_zero` and `Nonsingular.ne_zero` correct at all projective
   points, including the point at infinity and characteristics two and three?
4. Do `map_extendedIntegralModel_eq`, `baseResidueMap`, and
   `residue_extendedIntegralModel_eq` use the local-map instance and scalar towers correctly, and do
   they connect to the target's actual reduced curve rather than a merely isomorphic unbridged one?
5. Is `projectiveResidue_inertia` valid despite the noncanonical normalization choice? Audit the
   action on the valuation subring, the scalar comparison, and the passage to residue classes.
6. Is `pointSpecialization` total on the exact target point type, and does
   `pointSpecialization_inertia` prove the exact invariance needed by
   `torsion_fixed_of_invariant_injective`?
7. Did Stage 5 add any admission, axiom, target-equivalent assumption, or dependency whose axiom
   closure is not the standard trio?
8. Does the candidate honestly stop before torsion injectivity, leaving the original target and
   `FLT-TATE-UNRAMIFIED` open?

## Required executable checks

Independently run:

- direct elaboration of the changed file;
- a forced narrow build of the good-reduction target and methodology probe;
- a forced umbrella build of `FLT FLTMethodology`;
- declaration-level `#print axioms` for representative normalization, projective residue,
  equation/nonsingularity, total specialization, inertia invariance, and the unchanged target;
- changed-line prohibited-token and diff checks.

If a command cannot run, distinguish an operational failure from a mathematical finding. Existing
unrelated repository admissions or linter warnings are not candidate defects unless this diff changes
their closure.

## Result contract

Return exactly one leading verdict:

- `PASS-KERNEL-GREEN-PREFIX`;
- `REVISE-KERNEL-PREFIX` with exact bounded fixes;
- `FAIL-KERNEL-PREFIX` with a demonstrated mathematical, type, build, or axiom defect.

State the exact promotion scope. Even a pass may authorize only the new prerequisite declarations;
it must exclude torsion injectivity, `torsion_unramified_of_good_reduction`,
`FLT-TATE-UNRAMIFIED`, downstream closure, assumptions, and FLT.

Do not edit files, commit, push, mutate Helios or graph state, or supply the missing proof.

