# FLT-CHEBOTAREV rank-two deterministic adapter evidence

Date: 2026-07-30

Branch: `codex/ca-flt-chebotarev-rank-two-20260730`

Base: Brauer--Nesbitt reviewed milestone `8929b77866985a66fa7299c418a2fad2867cc606`

Initial production commit: `3e418d53b6de47dacf976a43f5416267e7b94751`

Independently reviewed repaired candidate: `ee0f49e`

## Produced declarations

- `FLT.CompatibleFamily.conjugacySaturation`
- `FLT.CompatibleFamily.charpoly_conjugate`
- `FLT.CompatibleFamily.charpoly_eq_of_dense_of_finrank_eq_two`
- `FLT.CompatibleFamily.nonempty_equiv_of_dense_charpoly_eq`
- `FLT.CompatibleFamily.nonempty_equiv_of_dense_conjugacy_charpoly_eq`
- `FLT.CompatibleFamily.globalArithFrob`
- `FLT.CompatibleFamily.charpoly_globalArithFrob`
- `FLT.CompatibleFamily.frobeniusOutside`
- `FLT.CompatibleFamily.FrobeniusConjugacyDensityAt`
- `FLT.CompatibleFamily.RatArithmeticFrobeniusConjugacyDensity`
- `FLT.CompatibleFamily.nonempty_representationEquiv_of_charFrob_eq_of_density`
- `FLT.CompatibleFamily.GaloisRepFamily.isCompatible_charFrob_eq`

The two density declarations are proposition definitions. They are not witnesses, axioms, or proof
claims.

## Mechanical verification

Targeted build:

```text
lake -H build FLT.GaloisRepresentation.CompatibleFamilyComparison
  FLTMethodology.Probes.ChebotarevRankTwo
Build completed successfully (3629 jobs).
Controller wall time: 3.06 s.
```

Umbrella build:

```text
lake -H build FLT FLTMethodology
Build completed successfully (9045 jobs).
Controller wall time: 6.22 s.
```

The controller build-attempt telemetry records 9,280 ms, the sum of those two final command wall
times. Earlier exploratory/recovery builds are not included in that bounded attempt duration.

Every theorem printed by `FLTMethodology.Probes.ChebotarevRankTwo` depends on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No theorem in the adapter depends on `sorryAx` or a custom density assumption.

The first independent execution review correctly rejected the original umbrella evidence because
the cached `FLT.olean` predated the final root import. After correcting the evidence defects, the
controller repeated both builds with hash checking against the repaired Lean source tree in a
writable worktree-local build directory. A second GPT rereview independently elaborated every exact
source and reproduced the axiom closures, but correctly returned `REVISE` because its read-only
sandbox could not write Lake artifacts.

Fable 5 then ran under an executable, tracked-source-read-only review contract. It independently
completed all four direct source elaborations, the 3,629-job targeted build, the 9,045-job umbrella
build, and every axiom audit. Its terminal verdict was `PASS` after 279,967 ms. The exact review is:

```text
methodology/review/flt-completion/chebotarev/
  rank-two-adapter-fable5-executable-review-20260730.md
```

This approves the deterministic adapter only.

## Independent design evidence

GPT-5.6 xhigh returned `REVISE` on the prior combined graph design and validated the split used
here. It independently elaborated the dense-set trace/determinant route, required conjugacy
saturation, narrowed the missing contract to `ℚ`, and required the representation-equivalence name.
Its exact prompt and response are retained beside this evidence packet.

Fable 5 produced a detailed literature-grounded static plan after 1,455,677 ms. It independently
confirmed the local-to-global map, conjugacy saturation, finite-exception quantification,
trace/determinant continuity route, explicit density contract, and the need for a separate density
graph node. Its bridge response terminated in plan mode while promising a later synthesis, so it is
retained as design evidence and is not counted as an implementation approval.

## Honest promotion boundary

This evidence closes the deterministic adapter, not the arithmetic Chebotarev theorem and not the
full compatible-family consumer. The control graph therefore records two distinct open obligations:

- `FLT-CHEBOTAREV-DENSITY` owns the unwitnessed arithmetic density proposition;
- `FLT-CHEBOTAREV` owns the remaining fixed-coefficient compatible-family consumer and depends on
  that density provider plus the proved rank-two Brauer--Nesbitt theorem.

The next gates are:

1. exact source review and operator decision for any T2 density assumption;
2. consumer-specific same-coefficient, determinant, and semisimplicity wiring;
3. a standard-trio proof of density for T3.
