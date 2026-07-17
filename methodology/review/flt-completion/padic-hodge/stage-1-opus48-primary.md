# Opus 4.8 primary early-interface design — p-adic Hodge

- Component: `padic-hodge`
- Obligation: `FLT-MLT-PADIC-HODGE`
- Agent/model: `opus48-primary-designer-d10` / `claude-opus-4-8`
- Backend/permission: `claude-code` / `suggest` (read-only requested)
- Difficulty/budget: `10` / `3600s`
- Attempt 1: `CANCELLED / NO VERDICT`; `320380ms`; session
  `951cf880-6587-4e74-a1f7-30372d2ecfdf`; `46` unique request IDs; `41435` input,
  `215015` cache creation, `1693198` cache read, `12654` output (`1962302` total including cache)
- Attempt 2 transport: `SUCCESS`
- Attempt 2 elapsed: `762611ms` (`real 762.62s`)
- Attempt 2 session: `b3108ae7-826b-46b9-8462-2f51dc627369`
- Attempt 2 unique request IDs: `53`
- Attempt 2 tokens: `30736` input, `236083` cache creation, `2031462` cache read,
  `43168` output (`2341449` total including cache)
- Verdict: **READY-FOR-GPT-REVIEW (conditioned)**
- Promotion: none; the obligation remains a definition gap and the build remains upstream-gated
- Full attempt-2 plan source:
  `/Users/philiphaynes/.claude/plans/primary-opus-4-8-early-delightful-falcon.md`

Attempt-2 request IDs, deduplicated across the primary Claude session and its subagents:

```text
req_011Cd7SPMARmFpziHTnUZWga
req_011Cd7SQdTVKfSnSFPV81PGP
req_011Cd7SR4PgHWkbAeh92B4oF
req_011Cd7SRMM9Ysd1s1kaokpmJ
req_011Cd7SRdrpes89efAi7DcF9
req_011Cd7SRnD85hxKQEJN2dTgX
req_011Cd7SS3tCPaieaWBhrt4z6
req_011Cd7SS4Jza9AokC8cVohuh
req_011Cd7SS8UXF44b3pNwa9Xy4
req_011Cd7SSMb4SggNkXGBeVYAX
req_011Cd7SScpqmTkQ2LE3NgYWm
req_011Cd7SSpT5xbBdeLGKuqVcN
req_011Cd7SSvaBfNFHmdjXM9mFi
req_011Cd7ST7J7LNSwQkaXxJy2m
req_011Cd7STSG826aY2psu8suzc
req_011Cd7STTYmAgGvAxMUciGE5
req_011Cd7STYviVTJZJcJSX3AEX
req_011Cd7STZYgD5QNnKufhiRdq
req_011Cd7SU3dNj37HiVYwjJFCf
req_011Cd7SUM9KkzLRK7KhRMWbM
req_011Cd7SUTeVVjg9jUFDhoicC
req_011Cd7SUXTC8e8rejzyuHcaf
req_011Cd7SV7aH8W3CrM4n9FVeL
req_011Cd7SVAX8msLunyoQeRYZt
req_011Cd7SVVbrKRmeC9qsAGpEK
req_011Cd7SVmxMU7RQsaDffK9pv
req_011Cd7SW9vCZRhhV8U2xQGrF
req_011Cd7SWA48c8xDNHt8FHrex
req_011Cd7SWUNhvjwtcAMaLWtmm
req_011Cd7SWivZkP8EDg2T3bwyR
req_011Cd7SX5s9ZLSvdvo685P5f
req_011Cd7SXZouocaZuHnWp3493
req_011Cd7SXyyxXDELowbD945jZ
req_011Cd7SYtzbo99wRtBVyQkYP
req_011Cd7SZ31oXEJPxLChVNyhM
req_011Cd7SZnPkkxsuXyQ3VHtwZ
req_011Cd7SaepNVKDjngQ44oUzK
req_011Cd7SbBqRuQu5yvLfM53S6
req_011Cd7SbYi3TxYe9y37jC9j4
req_011Cd7SbYzAXR368jSm1J5ge
req_011Cd7Sc21rn662mCcuGtx1h
req_011Cd7ScDfqp14KyCAtcFVsd
req_011Cd7SdF2EEhdYKyfQ9UDAi
req_011Cd7SeJFEKrZUwoKh195V3
req_011Cd7SgM6SJs27sYmrMtc5a
req_011Cd7SgjCTjzpYghYsPnmmY
req_011Cd7SoFgCLMsPc2QzUig2m
req_011Cd7Swhf7GEvbS3pHCFJMg
req_011Cd7TEm5xZ85gME3NzVcxZ
req_011Cd7TF4UEPmA5MUyZhbye1
req_011Cd7THQNcJibrwhAkKE55D
req_011Cd7TKC3FhM1uyABMNnKGZ
req_011Cd7TKjMv8wB2yaP6uxcjE
```

## Verdict — READY-FOR-GPT-REVIEW, conditioned

The interface design succeeded, but it deliberately does not pretend that the absent Fontaine
machinery exists. It proposes a two-tier boundary for
`FLT.ModularityLifting.Taylor2018.PadicHodge` and keeps the obligation in `definition-gap` state.

The selected source is Taylor 2018, Theorem 2.1.1, page 12. This component owns the local and
Hodge-theoretic hypotheses: matching Hodge–Tate weights, `ell` unramified in the totally real
field, crystallinity at every place above `ell`, the Fontaine–Laffaille interval, regular weight
data, and the weight-two finite-flat-to-crystalline bridge.

## Tier 1 — interfaces intended to elaborate now

The design freezes source-level data and predicates that can be stated using the present FLT and
Mathlib surface:

- a Hodge–Tate weight datum indexed by every place above `ell` and every local embedding;
- `IsRegularWeightData`, requiring distinct weights and cardinality equal to module rank;
- `HodgeTateWeightsMatch`, pointwise at every local embedding;
- `InFontaineLaffailleInterval`, provisionally using `ell - 1` consecutive integers; and
- the exact predicate that `ell` is unramified at every place above it, with its Mathlib spelling
  to be fixed by a probe.

These fields are intended to feed a `PadicHodgeData` bundle over a `GaloisRep F R V`.

## Tier 2 — explicit definition gaps

The repository currently has no period-ring or p-adic-Hodge API sufficient to define the following
faithfully:

- `GaloisRep.IsCrystallineAt`;
- `GaloisRep.hodgeTateWeightsAt`; and
- `GaloisRep.isCrystalline_of_isFlatAt_weightTwo`.

They therefore remain documented graph gaps, not fabricated opaque propositions and not admitted
theorems in a compiling green module. In particular, `GaloisRep.IsFlatAt` must not be defined to be
crystallinity.

The intended bridge has the mathematical shape:

```lean
theorem GaloisRep.isCrystalline_of_isFlatAt_weightTwo
    (hell : 2 < ell)
    (hrank : Module.finrank R V = 2)
    (v : Ω F)
    (hv : ↑ell ∈ v.asIdeal)
    (hflat : rho.IsFlatAt v) :
    rho.IsCrystallineAt v ∧
      (∀ τ, rho.hodgeTateWeightsAt v τ = {0, 1})
```

This is the load-bearing Raynaud / Fontaine–Laffaille / Breuil–Kisin mathematics. The statement is
only a target shape at this stage.

## Source-hypothesis ownership

| Taylor hypothesis | Owner in the proposed graph |
|---|---|
| RACAR `π` | `FLT-RACAR-DEF` |
| semisimplified residual agreement | `FLT-MLT-COEFFICIENTS` |
| Hodge–Tate weight match | `FLT-MLT-PADIC-HODGE` |
| residual irreducibility over the cyclotomic restriction | source/residual node |
| `ell` unramified in `F` | `FLT-MLT-PADIC-HODGE` |
| crystalline at every `v | ell` | `FLT-MLT-PADIC-HODGE` |
| `π_v` unramified at every `v | ell` | RACAR/source node |
| Fontaine–Laffaille interval | `FLT-MLT-PADIC-HODGE` |

The automorphic-side local-unramified condition is intentionally not placed inside the
Galois-side `PadicHodgeData` bundle.

## Dependency order

```text
FLT-MLT-COEFFICIENTS
  -> p-adic-Hodge Tier-1 signatures
  -> p-adic-Hodge Tier-2 definitions and weight-two bridge
  -> FLT-RACAR-DEF
  -> FLT-MLT-SOURCE
  -> selected-good and modularity-lifting consumers
```

The coefficient component must land first. The design also exposes that RACAR needs the weight
vocabulary supplied here before its source-faithful interface can be frozen.

## Bounded later build units

1. `BU-1`: Tier-1 signatures, `PadicHodgeData`, and a kernel probe;
2. `BU-2`: register the Tier-2 crystalline and weight declarations and bridge as named gaps;
3. `BU-3`: build the period-ring and `D_HT` / `D_cris` machinery;
4. `BU-4`: prove the weight-two finite-flat-to-crystalline bridge; and
5. `BU-5`: connect the abstract weight datum to actual `D_HT` output.

`BU-3` is explicitly unbounded and carries the dominant p-adic-Hodge risk. The design's proposed
application route attempts to keep the deepest general machinery off the immediate FLT integration
path by using the weight-two bridge, but that bridge itself remains serious mathematics.

## Soundness checks retained

- Finite-flat and crystalline are not definitionally equivalent.
- The `2 < ell` guard is load-bearing for the weight set `{0, 1}` to fit the proposed interval.
- Hodge–Tate weights must be indexed per embedding, not as one global multiset.
- Crystallinity and Hodge–Tate weights must be independent of the chosen stable lattice.
- Regularity must reject repeated weights such as `{0, 0}`.
- The weight multiset must have full cardinality equal to representation rank.
- The weight-two bridge must conclude exactly `{0, 1}`, not a higher-weight surrogate.

## Questions for independent review

1. Confirm whether “interval of length `ell - 1`” means `ell - 1` consecutive integers
   `[a, a + ell - 2]` or diameter `ell - 1`.
2. Confirm local-embedding rather than global-embedding indexing.
3. Confirm that automorphic local unramifiedness remains owned by RACAR/source.
4. Confirm the decision to parameterize Tier-1 by abstract weight data until `D_HT` exists.
5. Fix the exact Mathlib ramification predicate used to express `e(v) = 1`.

## Conditions before promotion

1. The independent review must settle the five interface questions above.
2. `FLT-MLT-COEFFICIENTS` must land first.
3. A build-enabled probe must establish that every Tier-1 signature elaborates.
4. The Tier-1 declarations must audit with only the standard axiom trio and no `sorryAx`.
5. The obligation must remain a definition gap until the Tier-2 content is actually built.

This result advances the design boundary; it does not close `FLT-MLT-PADIC-HODGE` and does not
authorize a source-design or proof-state promotion by itself.
