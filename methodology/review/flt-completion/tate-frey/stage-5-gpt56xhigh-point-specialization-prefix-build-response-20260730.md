# Stage 5 — GPT-5.6 xhigh point-specialization prefix build response

## Verdict

`KERNEL-GREEN-PREFIX`

The build proves the complete point-specialization and inertia-invariance prefix requested by Stage
5. It does **not** prove prime-to-residue-characteristic injectivity, so the unchanged theorem
`WeierstrassCurve.torsion_unramified_of_good_reduction` retains its original admission and
`FLT-TATE-UNRAMIFIED` remains open.

## Execution

- builder: `gpt56xhigh-builder`
- model: `gpt-5.6-sol`
- effort: `xhigh`
- session: `019faf9e-8726-76d3-9163-e2afa266e67b`
- transcript:
  `/Users/philiphaynes/.codex/sessions/2026/07/30/rollout-2026-07-30T06-43-49-019faf9e-8726-76d3-9163-e2afa266e67b.jsonl`
- bridge duration: `1,020,120 ms`
- model-task duration: `1,020,117 ms`
- input tokens: `13,055,030`, including `12,801,536` cached
- output tokens: `59,241`
- reasoning output tokens: `25,317`
- total tokens: `13,114,271`

## Proved declarations

All declarations below are in
`FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`.

Coordinate normalization and projective residue reduction:

- `ValuationSubring.HasUnitCoordinate`;
- `ValuationSubring.UnitCoordinateNormalization`;
- `ValuationSubring.exists_unitCoordinateNormalization`;
- `ValuationSubring.residueVector` and `residueVector_ne_zero`;
- `ValuationSubring.exists_unit_smul_eq_of_scaled`;
- `ValuationSubring.residue_pointClass_eq_of_scaled`;
- `ValuationSubring.unitCoordinateNormalization`;
- `ValuationSubring.residueRepresentative`, `residueRepresentative_of_ne_zero`, and
  `residueRepresentative_ne_zero`;
- `ValuationSubring.residue_pointClass_unit_smul`;
- `ValuationSubring.projectiveResidue` and `projectiveResidue_mk`.

Curve and specialization layer:

- `WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero`;
- `WeierstrassCurve.Projective.Nonsingular.ne_zero`;
- `ValuationSubring.extendedIntegralModel`;
- `ValuationSubring.map_extendedIntegralModel_eq`;
- `ValuationSubring.baseResidueMap`;
- `ValuationSubring.residue_extendedIntegralModel_eq`;
- `ValuationSubring.projectiveResidue_inertia`;
- `ValuationSubring.residueRepresentative_equation`;
- `ValuationSubring.residueRepresentative_nonsingular`;
- `ValuationSubring.projectiveResidue_nonsingularLift`;
- `ValuationSubring.pointSpecialization`;
- `ValuationSubring.pointSpecialization_inertia`.

The controller removed one new unnecessary-`simpa` linter warning without changing the declaration
or proof content.

## Controller validation

- direct `lake env lean FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`: passed; the only warning
  is the unchanged target admission;
- forced narrow build: passed, `2,505` jobs;
- forced `lake -H build FLT FLTMethodology`: passed, `9,047` jobs;
- `git diff --check`: passed;
- added-line prohibited-token scan: no new `sorry`, `admit`, `axiom`, or `opaque`;
- declaration-level audit of the key normalization, residue, model-compatibility, specialization, and
  inertia declarations: exactly `[propext, Classical.choice, Quot.sound]`;
- unchanged target audit: `[propext, sorryAx, Classical.choice, Quot.sound]`.

## Exact remaining boundary

The next theorem must prove:

```lean
Set.InjOn (A.pointSpecialization R k E hA)
  (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))
```

under `NeZero (n : IsLocalRing.ResidueField R)`. Only then can the existing
`torsion_fixed_of_invariant_injective` be applied to close the original good-reduction theorem.

This prefix is real reusable proof progress, but it is not obligation closure and has no graph
promotion effect by itself.

