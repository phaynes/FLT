# FLT-CHEBOTAREV rank-two deterministic adapter evidence

Date: 2026-07-30  
Branch: `codex/ca-flt-chebotarev-rank-two-20260730`  
Base: Brauer--Nesbitt reviewed milestone `8929b77866985a66fa7299c418a2fad2867cc606`

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
lake build FLT.GaloisRepresentation.CompatibleFamilyComparison
  FLTMethodology.Probes.ChebotarevRankTwo
Build completed successfully (3611 jobs).
```

Umbrella build:

```text
lake build FLT FLTMethodology
Build completed successfully (9045 jobs).
```

Every theorem printed by `FLTMethodology.Probes.ChebotarevRankTwo` depends on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No theorem in the adapter depends on `sorryAx` or a custom density assumption.

## Independent design evidence

GPT-5.6 xhigh returned `REVISE` on the prior combined graph design and validated the split used
here. It independently elaborated the dense-set trace/determinant route, required conjugacy
saturation, narrowed the missing contract to `ℚ`, and required the representation-equivalence name.
Its exact prompt and response are retained beside this evidence packet.

The literature-grounded Fable design was still pending when this mechanical evidence snapshot was
created and cannot be counted as approval.

## Honest promotion boundary

This evidence closes the deterministic adapter, not the arithmetic Chebotarev theorem and not the
full compatible-family consumer. The next gates are:

1. independent executable review of this implementation;
2. exact source review and operator decision for any T2 density assumption;
3. consumer-specific same-coefficient, determinant, and semisimplicity wiring;
4. a standard-trio proof of density for T3.

