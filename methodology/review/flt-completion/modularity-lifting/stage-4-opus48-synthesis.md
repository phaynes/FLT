# Stage 4 Opus 4.8 synthesis — modularity-lifting (`FLT-MLT-SOURCE`, `FLT-SGOOD-SELECTED`)

## Verdict: READY-FOR-GPT-REVIEW (conditioned)

Read-only synthesis. No repository file, task state, graph row, `source-design.ndjson` entry, Lean
source, obligation, or axiom is edited or promoted. Pins: Lean `v4.32.0-rc1`, Mathlib
`a3364faec42918fcd84a03a255b50570129f9ead`. Ground truth checked directly this turn against the live
tree (branch `methodology/varro-proof-program-20260716`).

Not `OBSTRUCTION`: the requested design work — freezing the five clean boundary units, fixing the
coefficient/source/consumer separation, assigning every disputed ownership, and stating the smallest
first buildable probe — is complete and reviewable, and the `FLT-SGOOD-SELECTED` probe builds *today*
with the standard trio. Not `NO-RESULT`: an exact, machine-grounded design exists. The gating on
`FLT-MLT-COEFFICIENTS` (REVISE, unlanded) and `FLT-RACAR-DEF` (BLOCKED) is a documented build-order
fact about `FLT-MLT-SOURCE`, not a defect. This matches the sibling dispositions
(`coefficients`, `padic-hodge` both READY-FOR-GPT-REVIEW conditioned).

## Context — why this exists

`FLT-404` owns two obligations that must stay separate objects (per
`methodology/TRACEABILITY.md:44-47`):

- **`FLT-SGOOD-SELECTED`** → the repository-local, proved-vocabulary condition bundle selected to
  match Taylor 2018 (home `FLT.ModularityLifting`), distinct from the already-proved `BlueprintSGood`
  (`FLT/ModularityLifting/Conditions.lean:28`) and never identified with `IsAutomorphicOfLevel S`.
- **`FLT-MLT-SOURCE`** → the literal Taylor 2018 Thm 2.1.1 interface (home
  `FLT.ModularityLifting.Taylor2018`), level-free GL₂/RACAR conclusion, never term-depending on
  `BlueprintSGood` or `IsAutomorphicOfLevel`.

Stage-1 Opus returned READY-FOR-GPT-REVIEW; stage-2 GPT returned **REVISE** (tame quotient on the
wrong layer, missing `supportAwayEll`/cyclotomic-degree/complex-embedding/single-coefficient owner,
unbridged dual/sign); stage-3 Fable returned **DESIGN-VIABLE** with a machine-checked five-unit
repair. `source-design.ndjson:9` is `lean_signature:false`,
`dor:"SYNTHESIS-RUNNING-TEMPORARY-PROBES-GREEN"`; next gate = "complete this Opus synthesis, then a
fresh GPT review before any SelectedGood probe persistence or source-contract promotion."

## Live ground truth (checked this turn, file:line)

| Fact | Location | Consequence |
|---|---|---|
| `cyclic_base_change` **ends in `sorry`** | `FLT/GaloisRepresentation/Automorphic.lean:194` | live but sorried; usable only as a shape reference, never applied in a clean decl |
| `hρtame` is a **generic-fibre** rank-one tame quotient over `ℚ_[p]ᵃˡᵍ`, `V : Type` | `Automorphic.lean:180-188` | tame quotient unit must be over `AlgebraicClosure ℚ_[ell]`, universe 0 |
| `hρflat` is an **integral-model** existential, `Module.rank R V₀ = 2`, `ρ₀.IsFlatAt v` | `Automorphic.lean:160-173` | flat descent is a *separate* integral unit, not `BlueprintSGood.isFlat` at the fibre |
| `hp : 2 < Module.finrank F (CyclotomicField p F)` is an **argument** of both `IsAutomorphicOfLevel` and `cyclic_base_change` | `Automorphic.lean:73,145` | cyclotomic degree is a standalone `Prop` at call sites, never a bundle field |
| `IsAutomorphicOfLevel` body guards only good primes `↑p ∉ v.1 ∧ v ∉ S` | `Automorphic.lean:90` | cannot carry an at-ℓ automorphic condition; H7 lives on the RACAR witness |
| `BlueprintSGood` = `det ∧ isUnramified ∧ traceOnJ=2 ∧ isFlat`, over local ring `R`, no `supportAwayEll` | `Conditions.lean:28-42` | repository parent; `traceOnJ` kept, `supportAwayEll` added by extension |
| `MLTPadicHodgeWeightData` landed kernel-green (stage-5 PASS): `AbstractWeightData`, `IsRegularWeightData`, `HodgeTateWeightsMatch`, `InFontaineLaffailleInterval a`, `EllUnramifiedInIntegers`, `AbstractWeightLocalData`, `GaloisRepDual`, guards | `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean` | weight/interval/dual vocabulary is a **landed** owner; `{-1,0}` at ρ |
| `MLTSourceBoundary` landed: `HasIntegralModel`, `IsSemisimplifiedResidualModel`, `SemisimpleResidualEquivalent`, `ResidualModelsAgreeAfterExtension`, `SemisimplifiedResidualModelsUnique` | `FLTMethodology/Probes/MLTSourceBoundary.lean` | residual-comparison relations exist as probe-green vocabulary |
| `MLTCoefficientData.lean` **absent**; `CoefficientData … O … rho` (explicit DVR `O`, `rhoBar`, `IsSemisimplifiedResidualModel`) | coefficients stage-3/4/5 | single coefficient owner is a **blocked** target (REVISE) |
| `SelectedGoodRepositoryBoundary.lean` **absent** | — | this is the first buildable probe to state |
| `FLT-RACAR-DEF` **BLOCKED** (`OBSTRUCTION` stands) | `source-design.ndjson:13` | H1/H2-attached/H7 + level-free conclusion are non-elaborable |

## Adjudication ledger (every disagreement, explicitly resolved)

| # | Dispute | Stage-1 Opus | Stage-2 GPT | Stage-3 Fable | **Synthesis ruling (with evidence)** |
|---|---|---|---|---|---|
| A1 | Tame-quotient layer | integral `SelectedGood` field | must be generic fibre | `HasGenericTameRankOneQuotient` over `ℚ_[ell]ᵃˡᵍ` | **Fable.** Verbatim `Automorphic.lean:180-188`; the consumer's `V,π,δ` live over `ℚ_[ell]ᵃˡᵍ`. |
| A2 | Fold tame quotient into repo bundle / strengthen `traceOnJ` | yes (replace `traceOnJ` w/ tame quotient) | no — unbridged strengthening | keep `traceOnJ`; tame quotient a *separate* unit | **Fable.** Keep three distinct boundaries (req. 4); `traceOnJ ↔ tame-quotient` is a *named open* obligation, not a silent identification. |
| A3 | Flatness layer | `BlueprintSGood.isFlat` / generic ρ | must be integral model | `HasFlatDescentAboveEll` (integral ρ₀) | **Fable + padic-hodge G-D.** `IsFlatAt` over the field `ℚ_[ell]ᵃˡᵍ` is vacuous (`HasFlatProlongationAt` needs finite reductions, `GaloisRep.lean:383-393`). Distinct unit. |
| A4 | Coefficient ring | `AlgebraicClosure ℚ_[ell]` valuation ring | needs explicit DVR `O` | single `CoefficientData … O …` owner | **GPT + coefficients.** One DVR-strength `O`; the fibre rep stays over `ℚ_[ell]ᵃˡᵍ` via the `O → E → ℚ_[ell]ᵃˡᵍ` tower. |
| A5 | One coefficient owner for H2 & H4 | separate `residualReduction r` | single selected model | `coeff.rhoBar` for both | **Fable.** H2 residual agreement *and* H4 cyclotomic irreducibility reference the *same* `coeff.rhoBar` (Ribet: distinct lattices give non-isomorphic non-ss reductions — CE-11). |
| A6 | Complex embedding | absent | must be explicit | `ComplexEmbeddingData` = data `(ℚ_[ell]ᵃˡᵍ) →+* ℂ` | **Fable.** Data, not `∃`/`Prop`; no such map in the pin, and an existential lets two hypotheses use different identifications (CE-12). |
| A7 | Cyclotomic degree | inside conclusion | separate hypothesis | `CyclotomicDegreeBound F ell` standalone | **Fable.** = `2 < Module.finrank F (CyclotomicField ell F)`, the literal `hp` arg (`Automorphic.lean:73,145`); a property of `(F,ell)`, never a bundle field. |
| A8 | Fontaine–Laffaille interval | diameter `ell-1` | one global `a`, `[a,a+ℓ-2]` | landed `InFontaineLaffailleInterval a` | **GPT + padic-hodge (landed).** One global `a`; `2 < ell` load-bearing (`weightTwo_fits_iff_two_lt`). |
| A9 | Sign / dual | `{0,1}` at ρ | dual/twist orientation must be exposed | `{-1,0}` at ρ, `{0,1}` at dual | **padic-hodge (verified).** `det ρ = ε`, `HT(ε)=-1` ⇒ weight sum `-1` ⇒ `{-1,0}` at ρ (`HardlyRamified/Defs.lean:107`, `Conditions.lean:37`). `{0,1}`-at-ρ is a soundness regression (G-C/CE-10). Dual transport G6/G7 named gaps. |
| A10 | Residual agreement mechanism | trace-based mixing | charpoly + semisimplicity | `IsSemisimplifiedResidualModel` | **GPT + Fable.** charpoly + semisimplicity (`MLTSourceBoundary.lean:48-63`); Brauer–Nesbitt uniqueness stays the separate `SemisimplifiedResidualModelsUnique` node, never assumed. |
| A11 | H4 irreducibility target | `F(ζ_ell)` on `residualReduction r` | — | `CyclotomicField ell F` on `coeff.rhoBar` | **Fable.** On `coeff.rhoBar` mapped to `CyclotomicField ell F`. Distinct from the consumer's `hρirred` (which is over the *solvable* descent field `E`, owned by the base-change route, not FLT-RESIDUAL-IMAGE). |
| A12 | `supportAwayEll` | omitted | required | `∀ w ∈ S, ↑ell ∉ w.asIdeal` | **GPT + Fable.** Added by `SelectedGoodRepository extends BlueprintSGood`; it is exactly `cyclic_base_change`'s `hS` (`Automorphic.lean:176`). |
| A13 | Consumer-exactness `example` (applies `cyclic_base_change`) | — | — | optional, quarantined | **Drop from the built umbrella (req. 6).** It inherits `sorryAx`; keep only as an ephemeral `/tmp` tripwire, never persisted in `FLTMethodology`. |
| A14 | Verdict for FLT-MLT-SOURCE now | READY (conditioned) | REVISE | DESIGN-VIABLE | **READY-FOR-GPT-REVIEW (conditioned).** SGOOD probe builds now; SOURCE frozen-for-review, gated on 3 owners. |

## Deliverable B — `FLT-SGOOD-SELECTED`: the five frozen boundary units (buildable now)

The five standard-trio-clean units from the Fable pass, **frozen unchanged**. They are structurally
the verbatim hypothesis slots of `cyclic_base_change` but reference *no* sorried declaration, so each
audits to `[propext, Classical.choice, Quot.sound]`.

1. `SelectedGoodRepository` — `BlueprintSGood ell rho S` **extended** with `supportAwayEll`
   (repository side; carries **no** automorphy, **no** crystalline/HT, **no** tame quotient).
2. `HasGenericTameRankOneQuotient` — generic-fibre tame rank-one quotient over `ℚ_[ell]ᵃˡᵍ`,
   verbatim `cyclic_base_change.hρtame`.
3. `HasFlatDescentAboveEll` — integral-model flat existential, verbatim `cyclic_base_change.hρflat`
   (`R V₀ : Type`, `Module.rank R V₀ = 2`, `ρ₀.IsFlatAt v`).
4. `CyclotomicDegreeBound F ell` — `2 < Module.finrank F (CyclotomicField ell F)` (property of
   `(F,ell)` only; passed at call sites, never a bundle field).
5. `ComplexEmbeddingData ell` — the *type* `(AlgebraicClosure ℚ_[ell]) →+* ℂ` (data).

Requirement 4 (three distinct boundaries): (2) generic-fibre tame quotient, (3) integral flat
descent, and `BlueprintSGood.traceOnJ` (trace-2) stay **separate**. The `traceOnJ ↔ tame-quotient`
bridge and the `HasIntegralModel ↔ HasFlatDescentAboveEll` implication are **named open** obligations,
not silent identifications.

### The smallest first buildable probe — exact file

`FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean` (register import in `FLTMethodology.lean`,
alphabetical block near line 21). Contains **only** the five units and their audits — no crystalline,
no Hodge–Tate, no RACAR, no bridge, no consumer-exactness `example`.

```lean
import FLT.GaloisRepresentation.Automorphic
import FLT.ModularityLifting.Conditions

namespace FLTMethodology.SelectedGoodBoundary

open IsDedekindDomain NumberField FLT.ModularityLifting
open scoped NumberField TensorProduct

/-- Repository-side boundary: the proved blueprint bundle plus support of `S` away from `ell`.
Carries NO automorphy conclusion, NO crystalline/HT condition, NO tame quotient. -/
structure SelectedGoodRepository
    {F : Type*} [Field F] [NumberField F]
    (ell : ℕ) [Fact ell.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[ell] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (rho : GaloisRep F R V)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop
    extends BlueprintSGood ell rho S where
  supportAwayEll : ∀ w ∈ S, ↑ell ∉ w.asIdeal

/-- Generic-fibre tame rank-one quotient — verbatim `cyclic_base_change.hρtame`, over
`AlgebraicClosure ℚ_[ell]`, `V : Type` (universe 0, as the consumer fixes it). -/
def HasGenericTameRankOneQuotient
    {F : Type*} [Field F] [NumberField F] (ell : ℕ) [Fact ell.Prime]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
    (rho : GaloisRep F (AlgebraicClosure ℚ_[ell]) V)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ w ∈ S, ∃ (π : V →ₗ[AlgebraicClosure ℚ_[ell]] AlgebraicClosure ℚ_[ell])
    (_ : Function.Surjective π)
    (δ : GaloisRep (w.adicCompletion F) (AlgebraicClosure ℚ_[ell]) (AlgebraicClosure ℚ_[ell])),
    localTameAbelianInertiaGroup w ≤ δ.ker ∧
    ∀ (g : Field.absoluteGaloisGroup (w.adicCompletion F)) (v : V),
      π ((rho.toLocal w) g v) = δ g (π v)

/-- Flat descent above `ell` — verbatim `cyclic_base_change.hρflat`: an integral model over a finite
free local `ℤ_[ell]`-algebra `R ⊆ ℚ_[ell]ᵃˡᵍ`, flat at every `v | ell`. `R V₀ : Type`,
`Module.rank R V₀ = 2`, exactly as the consumer states them. -/
def HasFlatDescentAboveEll
    {F : Type*} [Field F] [NumberField F] (ell : ℕ) [Fact ell.Prime]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
    (rho : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[ell] R) (_ : IsLocalRing R) (_ : IsDomain R)
    (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : Module.Finite ℤ_[ell] R) (_ : Module.Free ℤ_[ell] R) (_ : IsModuleTopology ℤ_[ell] R)
    (_ : Algebra R (AlgebraicClosure ℚ_[ell]))
    (_ : IsScalarTower ℤ_[ell] R (AlgebraicClosure ℚ_[ell]))
    (_ : ContinuousSMul R (AlgebraicClosure ℚ_[ell]))
    (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
    (_ : Module.Free R V₀) (_ : Module.rank R V₀ = 2)
    (ρ₀ : GaloisRep F R V₀)
    (r₀ : (AlgebraicClosure ℚ_[ell]) ⊗[R] V₀ ≃ₗ[AlgebraicClosure ℚ_[ell]] V),
  (ρ₀.baseChange (AlgebraicClosure ℚ_[ell])).conj r₀ = rho ∧
  ∀ v : HeightOneSpectrum (𝓞 F), ↑ell ∈ v.asIdeal → ρ₀.IsFlatAt v

/-- The cyclotomic-degree hypothesis of `IsAutomorphicOfLevel`, named once. A property of `(F, ell)`
only — deliberately NOT a field of any representation bundle. -/
def CyclotomicDegreeBound (F : Type*) [Field F] [NumberField F] (ell : ℕ) : Prop :=
  2 < Module.finrank F (CyclotomicField ell F)

/-- Taylor's fixed identification of the `ell`-adic and complex algebraic closures — data, not a
`Prop`; not constructible in the Mathlib pin; carried by `SourceHypotheses`. -/
def ComplexEmbeddingData (ell : ℕ) [Fact ell.Prime] : Type :=
  (AlgebraicClosure ℚ_[ell]) →+* ℂ

#check @SelectedGoodRepository
#check @HasGenericTameRankOneQuotient
#check @HasFlatDescentAboveEll
#check @CyclotomicDegreeBound
#check @ComplexEmbeddingData
#print axioms SelectedGoodRepository
#print axioms HasGenericTameRankOneQuotient
#print axioms HasFlatDescentAboveEll
#print axioms CyclotomicDegreeBound
#print axioms ComplexEmbeddingData

end FLTMethodology.SelectedGoodBoundary
```

Acceptance: `lake build FLTMethodology` green + every `#print axioms` line = exactly
`[propext, Classical.choice, Quot.sound]`. No `FLT`/`FermatsLastTheorem` root is touched (the probe
umbrella is not imported by them, `lakefile.toml`).

### Bridge B.2 (statement frozen, proof gated — NOT persisted now)

`selectedGood_to_source_local`: the repository conditions + coefficient data supply Taylor's local
H6 (crystalline at `v|ell`) and H8 (Fontaine–Laffaille interval) on `r = ρ₀ ⊗ ℚ_[ell]ᵃˡᵍ`. It
consumes **`HasFlatDescentAboveEll`** (not `BlueprintSGood.isFlat`) + weight-two data; load-bearing
content is **G4 finite-flat ⇒ crystalline weight-two** (dominant risk, padic-hodge Tier-2). Blocked on
`FLT-MLT-PADIC-HODGE` Tier-2 + `FLT-MLT-COEFFICIENTS`. H5 stays field-level; H1/H2/H7 stay with
RACAR; level-free ⇒ `IsAutomorphicOfLevel S` stays in `FLT-MLT`.

## Deliverable A — `FLT-MLT-SOURCE`: Taylor 2018 Thm 2.1.1 target shape (gated documentation)

Home `FLT.ModularityLifting.Taylor2018`. **Not persisted** as a compiling file until the three owners
land; `‹…›` marks Tier-2 graph gaps. Requirement 3 (one coefficient owner) and req. 2 (source ≠
repository) are enforced structurally: the block references *none* of the five repository units except
the neutral `ComplexEmbeddingData`, and both H2 & H4 reference the *same* `coeff.rhoBar`.

```lean
-- GATED TARGET SHAPE — elaborates only after MLTCoefficientData (FLT-MLT-COEFFICIENTS, REVISE),
-- the padic-hodge Tier-2 crystalline/HT providers (FLT-MLT-PADIC-HODGE), and the RACAR witness
-- (FLT-RACAR-DEF, BLOCKED). Documentation, not a probe. Do not create this file until owners land.
structure SourceHypotheses
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    (O : Type*) [CommRing O] [IsDiscreteValuationRing O] [Algebra ℤ_[ell] O] /- + coeff context -/
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
      (hV : Module.finrank (AlgebraicClosure ℚ_[ell]) V = 2)
    (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) where
  ι                    : ComplexEmbeddingData ell                     -- owner FLT-MLT-SOURCE (data)
  coeff                : ‹CoefficientData ell hell O hV r›             -- SINGLE owner, FLT-MLT-COEFFICIENTS
  weights              : AbstractWeightData F ell                     -- padic-hodge (landed)
  regular              : IsRegularWeightData 2 weights                 -- padic-hodge (landed)
  intervalBase         : ℤ                                            -- one global a
  fontaineLaffaille    : InFontaineLaffailleInterval intervalBase weights   -- H8, padic-hodge (landed)
  ellUnramifiedInF     : EllUnramifiedInIntegers F ell                -- H5, padic-hodge (landed)
  witness              : ‹RACAR F›                                     -- H1, FLT-RACAR-DEF (BLOCKED)
  witnessUnramAboveEll : ∀ v, (↑ell : 𝓞 F) ∈ v.asIdeal → ‹witness.IsUnramifiedAt v›  -- H7, RACAR
  residualAgree        : ‹SemisimpleResidualEquivalent coeff.rhoBar (attachedResidual ι witness)›  -- H2, on coeff.rhoBar
  weightsMatch         : ‹HodgeTateWeightsMatch (‹htWeights r ι›) (‹htWeights_of witness›)›       -- H3, gaps G2/G5
  cycloIrreducible     : GaloisRep.IsIrreducible
                           ((coeff.rhoBar).map (algebraMap F (CyclotomicField ell F)))  -- H4, SAME coeff.rhoBar
  crystallineAbove     : ∀ v, (↑ell : 𝓞 F) ∈ v.asIdeal → ‹r.IsCrystallineAt v›         -- H6, gap G1

def SourceContract … (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) : Prop :=
  SourceHypotheses F ell hell O hV r → ‹r.IsAutomorphic›   -- level-free RACAR sense, gap FLT-RACAR-DEF
```

## Explicit ownership assignment (requirement 5)

| Concern | Exact spelling | Owner | Where it sits | Status |
|---|---|---|---|---|
| cyclotomic degree | `CyclotomicDegreeBound F ell` = `2 < Module.finrank F (CyclotomicField ell F)` | `FLT-SGOOD-SELECTED` (defined in probe) | explicit argument at every `IsAutomorphicOfLevel`/`cyclic_base_change` call site; never a bundle field | green today |
| complex embedding | `ι : ComplexEmbeddingData ell` (data `(ℚ_[ell]ᵃˡᵍ)→+*ℂ`) | `FLT-MLT-SOURCE` | data field of `SourceHypotheses` | green today (type) |
| support away ℓ | `supportAwayEll : ∀ w ∈ S, ↑ell ∉ w.asIdeal` | `FLT-SGOOD-SELECTED` | field of `SelectedGoodRepository` (= consumer `hS`) | green today |
| p-adic-Hodge (weights/interval/ℓ-unram/dual) | `AbstractWeightData`, `IsRegularWeightData`, `InFontaineLaffailleInterval a`, `EllUnramifiedInIntegers`, `GaloisRepDual` | `FLT-MLT-PADIC-HODGE` **Tier-1** | reused in `SourceHypotheses` | **landed** kernel-green |
| p-adic-Hodge (crystalline/HT extract/flat⇒crys/place map/dual+det transport) | G1/G2/G4/G5/G6/G7 | `FLT-MLT-PADIC-HODGE` **Tier-2** | gaps; bridge B.2 | gaps (G4 dominant risk) |
| coefficient (one owner, H2 & H4) | `CoefficientData ell hell O hV r`, residual `coeff.rhoBar` | `FLT-MLT-COEFFICIENTS` | H2 residual agreement + H4 cyclotomic irreducibility, same `rhoBar` | **REVISE**, unlanded |
| RACAR witness / attached residual / H7 / conclusion | `witness`, `attachedResidual`, `witnessUnramAboveEll`, `r.IsAutomorphic` | `FLT-RACAR-DEF` | fields of `SourceHypotheses` + conclusion | **BLOCKED** |
| residual irreducibility over `F(ζ_ell)` (H4) | `IsIrreducible ((coeff.rhoBar).map (algebraMap F (CyclotomicField ell F)))` | `FLT-RESIDUAL-IMAGE` (consumes coeff owner) | field of `SourceHypotheses` | gap |
| `traceOnJ ↔ tame quotient` bridge; `HasIntegralModel ↔ HasFlatDescentAboveEll` | named open lemmas | `FLT-SGOOD-SELECTED` | separate, non-silent | open |

## Source / consumer ledger

**Providers `FLT-MLT-SOURCE` consumes:** `FLT-MLT-COEFFICIENTS` (REVISE), `FLT-MLT-PADIC-HODGE`
Tier-1 (landed) + Tier-2 (gaps), `FLT-RACAR-DEF` (BLOCKED), `FLT-RESIDUAL-IMAGE` (gap), and
`ComplexEmbeddingData` (self).

**Providers `FLT-SGOOD-SELECTED` consumes:** `BlueprintSGood` (proved), `GaloisRep` API +
`localTameAbelianInertiaGroup`/`toLocal`/`ker`/`baseChange`/`conj`/`IsFlatAt` (proved),
`CyclotomicField` (Mathlib). All green today.

**Live Lean consumer (shape only):** `cyclic_base_change` (`Automorphic.lean:137`, sorried) — the
five units are exactly its `hρtame`/`hρflat`/`hS`/`hp` slots plus `SelectedGoodRepository`
(`det`/`isUnramified`/`supportAwayEll`). It is **referenced as a shape, never applied** in any clean
declaration (req. 6).

**Future graph consumers (NOT yet Lean consumers — GPT stage-2 caveat honored):**
`FLT-DEF-FUNCTOR`, `FLT-LOCAL-GALOIS`, `FLT-HECKE-ACTION`, `FLT-MLT` (for SGOOD); `FLT-MLT`,
`FLT-RESIDUAL-IMAGE`, `FLT-AUX-LOCAL-FIELD` (for SOURCE). The deformation/local-Galois consumers
still use `BlueprintSGood.traceOnJ`; the future Hecke signature omits explicit `ell` — both must be
repaired downstream, not papered over here.

## Dependency order

```text
GREEN TODAY
  BlueprintSGood (proved)      MLTSourceBoundary residual relations (probe-green)
  MLTPadicHodgeWeightData Tier-1 (LANDED, kernel-green)
  cyclic_base_change (sorried; shape reference only, never applied)
        │
        ▼
  [P-A] Probes/SelectedGoodRepositoryBoundary.lean   ← FIRST BUILDABLE, standard-trio only
        (SelectedGoodRepository ∙ HasGenericTameRankOneQuotient ∙ HasFlatDescentAboveEll
         ∙ CyclotomicDegreeBound ∙ ComplexEmbeddingData)
        │
        ├───────────────┬─────────────────────────────┐
        ▼               ▼                             ▼
  [B-1] coefficients   [B-2] padic-hodge Tier-2       [B-3] RACAR witness + H7 +
  bridge — blocked on  crystalline/HT/flat⇒crys       attached residual + level-free
  MLTCoefficientData   (G1/G2/G4/G5/G6/G7) — gaps,     conclusion — BLOCKED (FLT-RACAR-DEF)
  (REVISE, unlanded)   G4 dominant risk
        │               │                             │
        └───────┬───────┴──────────────┬──────────────┘
                ▼                      ▼
  [B-4] SourceHypotheses/SourceContract freeze     [B-5] selectedGood_to_source_local
        (needs B-1 ∧ B-2 ∧ B-3)                          (needs B-1 ∧ B-2; G4 dominant)
                └──────────────┬──────────────────────────┘
                               ▼
  [OUT OF SCOPE] FLT-MLT terminal: level-free ⇒ IsAutomorphicOfLevel S
  [OPEN, named] traceOnJ ↔ tame-quotient bridge; HasIntegralModel ↔ HasFlatDescentAboveEll lemma
```

## Counterexamples / false weakenings rejected

1. `IsAutomorphicOfLevel ell … ∅` ≠ H7 — the predicate constrains only `v ∉ S`, `↑p ∉ v.1`
   (away from ℓ, `Automorphic.lean:90`); H7 is at `v | ell` on the RACAR witness.
2. `IsAutomorphicOfLevel S` ≠ the level-free source conclusion (that identification is the derived
   `FLT-MLT` theorem; keeping them apart is req. 2).
3. `BlueprintSGood.isFlat` at the generic fibre ≠ `hρflat` — `IsFlatAt` over `ℚ_[ell]ᵃˡᵍ` is vacuous
   (`HasFlatProlongationAt` forces finite reductions); flatness lives on the integral `ρ₀`.
4. `traceOnJ = 2` ⇎ tame rank-one quotient — no bridge either way; a tame quotient gives
   `trace σ = δ(σ) + (det/δ)(σ)` equal to 2 only under the specific unipotent shape; trace-2 does not
   yield an equivariant surjection `π` without representability. Both spellings coexist; bridge named.
5. H5 (`ell` unramified in `F`) ≠ H6 (`r` crystalline at `v|ell`) ≠ H7 (`π_v` unramified) — three
   distinct at-ℓ facts; crystallinity is not Galois unramifiedness at ℓ.
6. "unramified in `F`" ≠ "split completely" (SRC-012, rejected); `SL₂(𝔽_p)`-image (SRC-013) too strong.
7. H4 irreducibility must be **after** restriction to `F(ζ_ell)` on `coeff.rhoBar` — dihedral reps are
   irreducible over `F` yet reducible over `F(ζ_ell)`.
8. Trace equality ≠ residual agreement — charpoly + semisimplicity via `IsSemisimplifiedResidualModel`;
   uniqueness is the separate Brauer–Nesbitt node, never assumed.
9. Fontaine–Laffaille interval is `Set.Icc a (a + ℓ - 2)` with one global `a`; `2 < ell` is
   load-bearing (`weightTwo_fits_iff_two_lt`); `ℓ = 2` cannot inhabit regular weight two.
10. Sign regression: `{-1,0}` at ρ (`det ρ = ε`, `HT(ε)=-1`), `{0,1}` at `GaloisRepDual ρ`; stating
    `{0,1}` at ρ gives weight-sum `1 ≠ -1` (G-C).
11. Two residual models may differ (Ribet: distinct lattices → non-isomorphic non-ss reductions) —
    hence exactly one `CoefficientData` owner shared by H2 and H4.
12. `∃ ι` ≠ carrying `ι` — an existential complex embedding lets two hypotheses use different
    identifications; `ι` is data.
13. Universe drift: restating the flat existential with `R V₀ : Type*` or `finrank` (not
    `Module.rank`) breaks definitional slot-exactness with the consumer.
14. Persisting the consumer-exactness `example` (applies `cyclic_base_change`) would inject `sorryAx`
    into the built umbrella — forbidden; it stays an ephemeral `/tmp` tripwire only (req. 6).

## Stop-losses

- **S1 (`: Prop extends` syntax):** if `extends BlueprintSGood` misbehaves in the persisted build
  (parent-projection or instance-arg issue), fall back to a flat structure repeating the four
  blueprint fields + `supportAwayEll` with a `rfl`-level equivalence lemma to `BlueprintSGood`.
  Budget: half a day; no design change.
- **S2 (consumer drift):** the `/tmp` consumer-exactness `example` is the tripwire — if
  `cyclic_base_change`'s signature changes upstream, repair the *boundary* to the consumer, never the
  reverse; re-run the exactness elaboration before any re-freeze.
- **S3 (RACAR):** `FLT-RACAR-DEF` stays BLOCKED. No stub, placeholder `Prop`, or axiom for
  witness/attached/level-free vocabulary. `SourceHypotheses` stays documentation. If unblocking
  stalls beyond the programme window, escalate to re-decomposition of `automorphic-galois` — do not
  route around it here.
- **S4 (vocabulary duplication):** when `MLTCoefficientData` lands, `SourceHypotheses` spellings track
  it exactly; never fork a second coefficient/weight vocabulary in the MLT packet. Likewise reuse the
  landed `MLTPadicHodgeWeightData` names verbatim.
- **S5 (axiom policy):** acceptance for the probe is `lake build FLTMethodology` green + every
  `#print axioms` = exactly `[propext, Classical.choice, Quot.sound]`; any `sorryAx`/new axiom in a
  persisted declaration aborts the unit.
- **S6 (no state promotion):** `source-design.ndjson:9` stays untouched; `lean_signature` may flip only
  after the probe lands green **and** the mandatory GPT-5.6 xhigh review of this stage passes.

## First expected residual Lean goal

The probe is **vocabulary only** — the five units are `def`/`structure`, so there is **no residual
proof obligation inside it**; its acceptance gate is the five `#print axioms` lines all equal to
`[propext, Classical.choice, Quot.sound]`. The first thing that can *fail* is therefore an
**elaboration** goal, not a tactic goal:

> `SelectedGoodRepository … : Prop extends BlueprintSGood ell rho S` must elaborate and synthesize the
> parent projection `SelectedGoodRepository.toBlueprintSGood` with the standard trio (S1 fallback if
> `Prop extends` misbehaves).

The first genuine *proof* goal downstream (post-probe, low-risk warm-up) is the named-open implication

> `HasFlatDescentAboveEll ell rho → FLTMethodology.Taylor2018.HasIntegralModel ell rho`

discharged by dropping the flatness conjunct from the shared existential (structurally trivial). The
first *load-bearing* proof goal in the packet remains **G4**: from `ρ₀.IsFlatAt v` on the integral
model, conclude `r.IsCrystallineAt v ∧ (∀ τ, r.hodgeTateWeightsAt v τ = {-1,0})` — blocked on
padic-hodge Tier-2 period-ring vocabulary, the dominant mathematical risk.

## Verification (for the later, build-enabled task — NOT this read-only turn)

1. Create `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean` exactly as above; add
   `import FLTMethodology.Probes.SelectedGoodRepositoryBoundary` to `FLTMethodology.lean`.
2. `lake build FLTMethodology`; then `lake env lean` the probe and confirm the five standard-trio
   `#print axioms` lines (authoritative per `methodology/FROZEN-BASELINE.md`).
3. Run the consumer-exactness elaboration in a `/tmp` file (applies `cyclic_base_change` to the trio)
   and confirm exit 0 — evidence only, discarded, never persisted.
4. `rg`-gate: no `sorry`/`sorryAx`/`axiom` introduced under `FLT/` or `FermatsLastTheorem`;
   `git status` clean except the two intended files. `source-design.ndjson` unchanged.

## Conditions before any promotion (none authorized here)

1. Fresh GPT-5.6 xhigh review confirms the five frozen units, the single `coeff.rhoBar` owner across
   H2/H4, the `{-1,0}`-at-ρ sign, the three-distinct-boundaries ruling, and the ownership table.
2. `FLT-MLT-COEFFICIENTS` and the padic-hodge Tier-2 providers land kernel-green before B.2/B.4 may
   elaborate; `FLT-RACAR-DEF` remains BLOCKED, so `SourceHypotheses`/`SourceContract` stay documentation.
3. The persisted probe contains only the five units; every `#print axioms` returns the trio.

Until these hold this is a reviewed design candidate — not a completed component, not a proof-state
promotion.
