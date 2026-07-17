# Opus 4.8 primary early-interface design — coefficients

- Component: `coefficients`
- Obligation: `FLT-MLT-COEFFICIENTS`
- Agent/model: `opus48-primary-designer-d10` / `claude-opus-4-8`
- Backend/permission: `claude-code` / `suggest` (read-only requested)
- Difficulty/budget: `10` / `3600s`
- Attempt 1: `CANCELLED / NO VERDICT`; `320220ms`; session
  `7d4c3515-dc6f-4bfd-9414-f604d9921958`; `41` unique request IDs; `22936` input,
  `158870` cache creation, `1135112` cache read, `9923` output (`1326841` total including cache)
- Attempt 2 transport: `SUCCESS`
- Attempt 2 elapsed: `772197ms` (`real 772.21s`)
- Attempt 2 session: `2bef9c60-d377-4722-b3f1-4340eac066c5`
- Attempt 2 unique request IDs: `60`
- Attempt 2 tokens: `27643` input, `290294` cache creation, `2399846` cache read,
  `42424` output (`2760207` total including cache)
- Verdict: **READY-FOR-GPT-REVIEW**
- Promotion: none; independent review and the Wave-0 elaboration gate remain outstanding
- Full attempt-2 plan source:
  `/Users/philiphaynes/.claude/plans/primary-opus-4-8-early-serialized-ladybug.md`

Attempt-2 request IDs, deduplicated across the primary Claude session and its subagents:

```text
req_011Cd7SPPGgT98RgUxEipqc6
req_011Cd7SRDe3aSE3329kygbf2
req_011Cd7SS4acgSpYmxdPahxB5
req_011Cd7SSbF6A3JxGVHMb8Wvf
req_011Cd7SSkcu2mF7FPULj4tPo
req_011Cd7SSnR3tYQ8f3HwvMJno
req_011Cd7SSrtBSrA4dvgPY3Zy7
req_011Cd7ST9kSYmf7UYwXfYyjA
req_011Cd7STJpeScTZzaMtPqFcm
req_011Cd7STjQzkC8YpLSb1ysX8
req_011Cd7STje9CYdoAnjykhrsC
req_011Cd7STqLwg1YWMTsAzA57B
req_011Cd7SU8Le9Y9zCLEqWUNwF
req_011Cd7SUCnnY2JDNm6syWWEF
req_011Cd7SUPmLJNGAFYTdM6XP1
req_011Cd7SUT7kNLC8ikZ18juep
req_011Cd7SUjzFuecmirxYZ7zWZ
req_011Cd7SUs8csUSjjt6PfQ9pd
req_011Cd7SV94pmWYV2ELvcL75z
req_011Cd7SVAA4Bi8zCPvdyPcHT
req_011Cd7SVPq5nGkjkfZZUpwoK
req_011Cd7SVeQRzWgrY8bBQwD2b
req_011Cd7SVtrake2Wv7n1cEn5L
req_011Cd7SWHqCT7hAsYmXUuRyz
req_011Cd7SWVTCBQzndX91XfEhL
req_011Cd7SWmuQGspJTwEUsYtTf
req_011Cd7SXAd97Jhu36qiTepeD
req_011Cd7SXAtWw7JYazy4nEaJK
req_011Cd7SXL98ipuho1ofEdHgX
req_011Cd7SXbe3aPchY6egdqc8b
req_011Cd7SXzQ1mwAMTiZf9w4sM
req_011Cd7SYJqXr7BaJVJj2xYxi
req_011Cd7SYKxznahmLMSmsoAqE
req_011Cd7SYYCSxRksfMm39qRsB
req_011Cd7SYuBGQRYootyEbVqmd
req_011Cd7SZGyCKVziC8MhtBD4W
req_011Cd7SZP7HFWgrWr9uYKP2X
req_011Cd7SZqneMDLHarZ6DZ64W
req_011Cd7SZsCUhHPBjFhbJv7yV
req_011Cd7Sany1kaiA8Vw7as4Yi
req_011Cd7Sb3VNzqr64WjdvpPoq
req_011Cd7SbmJLFfqLmLdFbYwJv
req_011Cd7ScNQT3TmUhA22nsy7w
req_011Cd7Sczoi5iLe2qgqdNEb8
req_011Cd7Sdb4EkgXunKCRCw6fh
req_011Cd7SdyC18GJtEF1gRGyvA
req_011Cd7SeH62LChbnPz1BRxHM
req_011Cd7Sf4fgzpqZFdhP646R6
req_011Cd7SfkgV5bcgKmsbyrQdF
req_011Cd7SfsUGizzhjmwWBdeST
req_011Cd7SgPDvdBGEy1FvXhRPj
req_011Cd7Sh5qw1itvrBQPkNdgL
req_011Cd7ShfKaTPBbP6JzNFhh8
req_011Cd7SiAvZF77fWtVbcgoQm
req_011Cd7SjMfzQBeY7zTbJGn5e
req_011Cd7Sm9reTxDgNaoLt8x9t
req_011Cd7SoJ73Ur9e5LSCstBEx
req_011Cd7SttfZXYBeobWiNwxBs
req_011Cd7TKL3xP56jC3z8vzUXm
req_011Cd7TM96hWcguMonNyiv6A
```

## Verdict — READY-FOR-GPT-REVIEW

The design freezes a source-faithful coefficient package for Taylor 2018, Theorem 2.1.1. It does
not claim the missing mathematics is proved. The proposed home is
`FLT.ModularityLifting.Taylor2018.Coefficients`, with the primary consumer-facing declaration
`FLT.ModularityLifting.Taylor2018.CoefficientData`.

The package fixes the following coefficient tower:

- `O`: a discrete valuation ring finite/free over `ℤ_[p]`;
- `E`: the fraction field of `O`, with the required topology and scalar tower;
- `k`: `IsLocalRing.ResidueField O`;
- an integral, Galois-stable `O`-model of the `E`-valued representation;
- reduction through the maximal ideal;
- a semisimplified residual representation; and
- comparison after scalar extension to an algebraic closure of `k`.

It retains the reviewed maximal-ideal-kernel repair
`IsLocalRing.maximalIdeal O ≤ RingHom.ker (algebraMap O k)`, which prevents an arbitrary generic
base change from masquerading as residual reduction.

## Reused kernel-green surface

The design reuses the five scaffold relations already banked in
`FLTMethodology/Probes/MLTSourceBoundary.lean`:

- `HasIntegralModel`;
- `IsSemisimplifiedResidualModel`;
- `SemisimpleResidualEquivalent`;
- `ResidualModelsAgreeAfterExtension`; and
- `SemisimplifiedResidualModelsUnique`.

Those declarations previously audited with only the standard axiom trio. This design does not
upgrade the proposition `SemisimplifiedResidualModelsUnique` into a proved theorem.

## Explicitly absent obligations

The proposed interface separates five obligations instead of hiding them in the bundle:

1. `A1` — stable-lattice existence for a continuous finite-dimensional `E`-valued Galois
   representation;
2. `A2` — completeness, Noetherian, and finite-residue-field glue for `O`;
3. `A3` — existence of a matching semisimplified residual representation;
4. `A4` — lattice-independence / Brauer–Nesbitt uniqueness, owned by
   `FLT-BRAUER-NESBITT`; and
5. `A5` — the `CoefficientData` consumer bundle itself.

The design classifies A1 and A4 as the research-heavy proof obligations. A2 and A3 are narrower
library/glue tasks. A5 is a packaging task after the preceding interfaces are available.

## Frozen interface shape

`CoefficientData ρ` is intended to carry:

- a free finite rank-two `O`-module `V₀`;
- an integral representation `ρ₀ : GaloisRep F O V₀`;
- an equivalence `E ⊗[O] V₀ ≃ₗ[E] V` compatible with `ρ`;
- a free finite residual module `W`;
- `ρ̄ : GaloisRep F (ResidueField O) W`; and
- proof that `ρ̄` is a semisimplified residual model of `ρ₀`.

Because Lean structures cannot directly take instance fields in bracket syntax, the proposed
bundle carries module and finiteness instances as ordinary fields, to be installed by consumers
with `letI`. The design recommends retaining both the proposition-level `HasIntegralModel` and the
data-level `CoefficientData` interface.

## Dependency order

```text
existing Mathlib and FLT representation APIs
  -> coefficient context O / E / k
  -> completeness and finite-residue glue
  -> stable integral model
  -> residual reduction
  -> semisimplification existence
  -> Brauer-Nesbitt uniqueness after scalar extension
  -> CoefficientData
  -> padic-hodge / RACAR / MLT source / selected-good consumers
```

## Bounded later build units

1. `BU-1`: coefficient context, `CoefficientData`, and signature probes;
2. `BU-2`: completeness, Noetherian, and finite-residue glue;
3. `BU-3`: stable-lattice existence;
4. `BU-4`: semisimplification existence and rank preservation; and
5. `BU-5`: the rank-two odd-characteristic Brauer–Nesbitt route.

Only `BU-1` is expected to close the T1 signature gate. The remaining units are T2/T3 proof work.

## Soundness checks retained

- Equal trace alone is insufficient; the residual comparison must retain full characteristic
  polynomial equality, equal rank, and semisimplicity.
- The residual algebra must be the residue field, not an arbitrary `O`-algebra.
- `IsDiscreteValuationRing O` is a source-faithful hypothesis, not a consequence of the weaker
  local finite-algebra assumptions.
- The Brauer–Nesbitt terminal must not be generalized to an arbitrary imperfect field.
- RACAR, Hodge–Tate, crystalline, Fontaine–Laffaille, and cyclotomic-restriction hypotheses remain
  outside this component.

## Conditions before promotion

1. The independent GPT reviewer must adjudicate the DVR strengthening.
2. It must choose or approve the bundle-plus-proposition packaging.
3. A Wave-0-enabled Lean probe must confirm that `CoefficientData` and the coefficient context
   elaborate.
4. Every promoted green declaration must audit without `sorryAx` and with only the standard axiom
   trio.

Until those conditions hold, this is a reviewed design candidate, not a completed coefficient
component and not a proof-state promotion.
