# Stage 3 Fable 5 diversity design — modularity lifting (repaired)

## Verdict: DESIGN-VIABLE

Read-only. All probes ran in temporary files under `/tmp` (deleted after use) against the pinned
toolchain `leanprover/lean4:v4.32.0-rc1` and Mathlib `a3364fa`, using only prebuilt oleans. No
repository file, task state, obligation, axiom, or `source-design.ndjson` row was changed.

## Context

`FLT-MLT-SOURCE` / `FLT-SGOOD-SELECTED` (component `modularity-lifting`, difficulty 10) received a
stage-2 GPT-5.6 xhigh verdict of REVISE: the stage-1 Opus design placed the tame rank-one quotient
on an integral representation while the live `cyclic_base_change` consumer requires it on the
`AlgebraicClosure ℚ_[ell]` generic fibre; it omitted `supportAwayEll`, the cyclotomic-degree
hypothesis, the complex embedding, and a single shared coefficient/residual-model owner; and it left
the dual/sign convention unbridged. This design independently repairs the interface against the
actual Lean types and machine-checks the repaired boundary.

## Machine-checked evidence (this session, temporary files)

**Probe 1** (five definitions, all elaborated; every `#print axioms` returned exactly
`[propext, Classical.choice, Quot.sound]`):

- `SelectedGoodRepository` — `BlueprintSGood ell rho S` + `supportAwayEll`;
- `HasGenericTameRankOneQuotient` — verbatim `cyclic_base_change.hρtame` over `ℚ_[ell]ᵃˡᵍ`;
- `HasFlatDescentAboveEll` — verbatim `cyclic_base_change.hρflat` (integral-model existential);
- `CyclotomicDegreeBound` — `2 < Module.finrank F (CyclotomicField ell F)`;
- `ComplexEmbeddingData` — the type `(ℚ_[ell]ᵃˡᵍ) →+* ℂ`.

**Probe 2** (consumer-exactness, exit 0): with `hsel : SelectedGoodRepository`,
`htame : HasGenericTameRankOneQuotient`, `hflat : HasFlatDescentAboveEll`, the term

```lean
cyclic_base_change hF p hp hpE hV ρ hρirred hsel.det hflat S
  hsel.supportAwayEll hsel.isUnramified htame
```

elaborates and closes the exact `IsAutomorphicOfLevel` iff-goal of the live consumer
(`FLT/GaloisRepresentation/Automorphic.lean:137-194`). This is definitional slot-exactness, not
analogy. The field→`IsLocalRing` priority-100 instance
(`Mathlib/RingTheory/LocalRing/Basic.lean:133`) lets the bundle instantiate at the generic fibre
`R := ℚ_[ell]ᵃˡᵍ` (`Algebra ℤ_[ell]` and topology instances resolve via
`Automorphic.lean:112-117` and `PadicAlgCl` = `abbrev` for `AlgebraicClosure ℚ_[p]`,
`Mathlib/NumberTheory/Padics/Complex.lean:54`).

This probe may never be persisted as a green declaration: it consumes the sorried
`cyclic_base_change`, so its axiom closure contains `sorryAx`. It is evidence, recorded here, and
survives in the persisted probe only as an `example` (elaborated, discarded, never promoted) or is
dropped entirely if the next review demands strict standard-trio file purity.

**Absence checks**: `FLTMethodology/Probes/MLTCoefficientData.lean` and
`FLTMethodology/Probes/MLTPadicHodgeWeightData.lean` do not exist — the coefficients (stage-4
synthesis) and p-adic-Hodge (stage-3 diversity) designs are frozen but unlanded. Every source
bridge below is therefore genuinely blocked, not merely unreviewed.

## New findings against the prior stages (hostile-review deltas)

1. **The stage-2 reviewed unit is itself incomplete.** Its next-unit list (only
   `SelectedGoodRepository` + `HasGenericTameRankOneQuotient` + audits) cannot feed the live
   consumer: `cyclic_base_change.hρflat` demands the *integral-model* flat existential
   (`ρ₀ : GaloisRep F R V₀` over a finite free local `ℤ_[ell]`-algebra, flat at `v | ell`, with
   `(ρ₀.baseChange (ℚ_[ell]ᵃˡᵍ)).conj r₀ = ρ`), which is **not** projectable from
   `BlueprintSGood.isFlat` at the generic fibre — `IsFlatAt` over a field is the wrong layer
   (confirming the padic-hodge stage-3 "flatness must be on the integral model" finding). A third
   unit `HasFlatDescentAboveEll` is required; Probe 2 machine-demonstrates sufficiency of the trio.
2. **Two BlueprintSGood fields are dead at the generic fibre.** Probe 2 consumes `det`,
   `isUnramified`, `supportAwayEll` — never `traceOnJ`, never `isFlat`. The `traceOnJ = 2` ↔
   tame-rank-one-quotient bridge (in either direction) is an open obligation, exactly as GPT
   flagged ("strengthened `BlueprintSGood.traceOnJ` without a bridge"); the deformation consumers
   (`FLT/Deformations/LiftFunctor.lean:128-135` `traceConditionFunctor`) still use trace-two, so
   both spellings must coexist with a named open bridge, not a silent identification.
3. **The cyclotomic-degree hypothesis is a property of `(F, ell)` only** — it is an *argument* of
   `IsAutomorphicOfLevel` (`Automorphic.lean:73`), not a property of `rho`. It must be a named
   standalone `Prop` (`CyclotomicDegreeBound`), passed at consumer call sites, never a field of the
   representation bundle (a field would block instantiating the bundle before choosing the level
   route and would wrongly suggest it is a condition on `rho`).
4. **The complex embedding must be data, not a `Prop`.** No `ℂ ≃+* ℚ_[ell]ᵃˡᵍ` or embedding exists
   in the Mathlib pin; existence is a nonconstructive cardinality/transcendence argument. Consumers
   must carry `ι : (ℚ_[ell]ᵃˡᵍ) →+* ℂ` as a `Type`-valued datum (field homs are automatically
   injective). An `∃`-form would let two hypotheses silently use different identifications, which
   is precisely the class of bug the stage-2 review flagged for residual models.
5. **Universe pinning.** `cyclic_base_change` fixes `V : Type`, and its flat existential quantifies
   `R V₀ : Type` (Type 0), with `Module.rank R V₀ = 2` (not `finrank`). The boundary definitions
   must reproduce these choices verbatim (probed); a `Type*` restatement of the existential would
   not be definitionally the consumer's slot.

## The repaired design

### Unit P-A — first buildable no-axiom probe (green today)

Persist `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean`, register in
`FLTMethodology.lean` (alphabetical import block), containing exactly the five probed units and
their standard-trio audits — nothing else (no crystalline, no Hodge–Tate, no RACAR placeholders):

```lean
import FLT.GaloisRepresentation.Automorphic
import FLT.ModularityLifting.Conditions

namespace FLTMethodology.SelectedGoodBoundary

open IsDedekindDomain NumberField FLT.ModularityLifting
open scoped NumberField TensorProduct

-- (use modern syntax `: Prop extends`, per the 4.32 linter warning observed in the probe)
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

/-- Generic-fibre tame rank-one quotient — verbatim `cyclic_base_change.hρtame`,
over `AlgebraicClosure ℚ_[ell]`, `V : Type` (universe 0, as the consumer fixes it). -/
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

/-- Flat descent above `ell` — verbatim `cyclic_base_change.hρflat`: an integral model over a
finite free local `ℤ_[ell]`-algebra `R ⊆ ℚ_[ell]ᵃˡᵍ`, flat at every `v | ell`. `R V₀ : Type`,
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

/-- The cyclotomic-degree hypothesis of `IsAutomorphicOfLevel`, named once. A property of
`(F, ell)` only — deliberately NOT a field of any representation bundle. -/
def CyclotomicDegreeBound (F : Type*) [Field F] [NumberField F] (ell : ℕ) : Prop :=
  2 < Module.finrank F (CyclotomicField ell F)

/-- Taylor's fixed identification of the `ell`-adic and complex algebraic closures — data, not a
`Prop`; not constructible in the Mathlib pin; carried by `SourceHypotheses`. -/
def ComplexEmbeddingData (ell : ℕ) [Fact ell.Prime] : Type :=
  (AlgebraicClosure ℚ_[ell]) →+* ℂ

-- #print axioms on all five: must be exactly [propext, Classical.choice, Quot.sound]
end FLTMethodology.SelectedGoodBoundary
```

Optionally (subject to the next review's file-purity ruling), a *separate*
`SelectedGoodConsumerExactness.lean` holds the Probe-2 `example` (statement-level tripwire against
`cyclic_base_change` drift; the `example` is never promoted, but the file knowingly elaborates
against a sorried theorem — keep it out of P-A either way).

Note the relation to `FLTMethodology.Taylor2018.HasIntegralModel`
(`Probes/MLTSourceBoundary.lean:23-39`): `HasFlatDescentAboveEll` = that existential + the
`hW`-rank clause + the flatness conjunct. Do not merge them: `HasIntegralModel` is the
coefficients-boundary bank; `HasFlatDescentAboveEll` is the consumer-verbatim slot. A later
one-line implication lemma may relate them (bounded unit, not required now).

### Separation of repository bundle from Taylor's source hypotheses (requirement 2)

Three-object separation, unchanged and enforced: `BlueprintSGood`/`SelectedGoodRepository`
(repository, proved vocabulary, no automorphy conclusion) ≠ `SourceHypotheses`/`SourceContract`
(Taylor 2018 Thm 2.1.1, level-free GL₂/RACAR conclusion) ≠ `IsAutomorphicOfLevel S` (derived
quaternionic predicate; `FLT-MLT` terminal). The source theorem must not term-depend on
`BlueprintSGood` or `IsAutomorphicOfLevel` (stage-2 requirement): `SourceHypotheses` mentions
none of the P-A units except `ComplexEmbeddingData`.

### One coefficient/lattice/residual-model owner (requirement 3)

The single owner is the coefficients stage-4 frozen `CoefficientData ell hp O hV rho` (explicit
`(O : Type*)` DVR choice-datum; `StableLatticeData` with `r0 : E ⊗[O] V0 ≃ₗ[E] V` and
`(rho0.baseChange E).conj r0 = rho`; residual `rhoBar` with
`IsSemisimplifiedResidualModel rho0 rhoBar`). In the repaired `SourceHypotheses`:

- H2 residual agreement references `coeff.rhoBar` — the one selected model;
- H4 cyclotomic irreducibility is stated on **the same** `coeff.rhoBar`
  (`GaloisRep.IsIrreducible ((coeff.rhoBar).map (algebraMap F (CyclotomicField ell F)))`);
- cross-residue-field comparison only through `AgreeInResidualClosure`
  (`AlgebraicClosure (ZMod ell)`, both embeddings explicit).

No hidden existential reductions anywhere; Ribet-style lattice-dependence of *non-semisimplified*
reductions is exactly why (counterexample 11 below).

### Weight data and forced dual/sign convention (requirement 4)

Adopt unchanged from the reviewed padic-hodge stage-3 (no crystalline placeholders):
`AbstractWeightData` indexed by `F →+* AlgebraicClosure ℚ_[ell]`; regularity =
rank/cardinality + `Multiset.Nodup` per embedding; the exact interval
`Set.Icc a (a + (ell : ℤ) - 2)` with **one global `a`** (not diameter); field unramifiedness via
`Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ell : ℤ)})`. Sign: repository consumers force
`det rho = ε` with `HT(ε) = −1`, so the source boundary is stated **at `rho` with weights
`{-1, 0}`**; `GaloisRepDual rho` (`σ ↦ (rho σ⁻¹).dualMap`) carries `{0, 1}` (étale-H¹ side);
dual-transport (G6/G6′) and weight-sum-equals-determinant-weight (G7) stay named audit-bridge
gaps. `IsCrystallineAt`, HT-extraction, and flat⇒crystalline (G1/G2/G4) remain gaps — never
stubbed, never citation-discharged.

### Exact owners of the three flagged hypotheses (requirement 5)

| Hypothesis | Exact spelling | Owner | Where it sits |
|---|---|---|---|
| cyclotomic degree | `CyclotomicDegreeBound F ell` | `FLT-SGOOD-SELECTED` (defined in P-A) | explicit argument at every `IsAutomorphicOfLevel`/`cyclic_base_change` call site; never a bundle field |
| at-ℓ RACAR unramifiedness (H7) | `∀ v, ↑ell ∈ v.asIdeal → witness.IsUnramifiedAt v` | `FLT-RACAR-DEF` (BLOCKED) | field on the RACAR witness inside `SourceHypotheses`; discharged in applications by good reduction |
| complex embedding | `ι : ComplexEmbeddingData ell` (data) | `FLT-MLT-SOURCE` | data field of `SourceHypotheses`; consumed by the RACAR attached-representation interface |

### Blocked source bridges (requirement 6) — target shapes only, non-elaborable today

`SourceHypotheses` (home `FLT.ModularityLifting.Taylor2018`, gated on all three owners landing):

```lean
-- GATED TARGET SHAPE — elaborates only after MLTCoefficientData (FLT-MLT-COEFFICIENTS),
-- MLTPadicHodgeWeightData (FLT-MLT-PADIC-HODGE), and the RACAR witness (FLT-RACAR-DEF, BLOCKED).
structure SourceHypotheses
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    (O : Type*) [CommRing O] [IsDiscreteValuationRing O] [Algebra ℤ_[ell] O] /- + stage-4 context -/
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V] /- … -/
    (hV : Module.finrank (AlgebraicClosure ℚ_[ell]) V = 2)
    (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) where
  ι                    : ComplexEmbeddingData ell                    -- owner: FLT-MLT-SOURCE (data)
  coeff                : CoefficientData ell ‹_› O hV r              -- single owner, stage-4 exact
  weights              : AbstractWeightData F ell                    -- padic-hodge stage-3 exact
  regular              : ‹weights regular›                           -- Nodup form
  intervalBase         : ℤ                                           -- ONE global a, explicit data
  fontaineLaffaille    : ‹all weights ⊆ Set.Icc intervalBase (intervalBase + (ell:ℤ) - 2)›
  ellUnramifiedInF     : ‹EllUnramifiedInIntegers F ell›
  witness              : ‹RACAR F›                                    -- BLOCKED: FLT-RACAR-DEF
  witnessUnramAboveEll : ∀ v, ↑ell ∈ v.asIdeal → ‹witness.IsUnramifiedAt v›  -- H7, at owner
  residualAgree        : ‹SemisimpleResidualEquivalent coeff.rhoBar (attachedResidual ι witness)›
  weightsMatch         : ‹HodgeTateWeightsMatch r witness ι›          -- gaps G2/G5
  cycloIrreducible     : GaloisRep.IsIrreducible
                           ((coeff.rhoBar).map (algebraMap F (CyclotomicField ell F)))  -- same rhoBar
  crystallineAbove     : ∀ v, ↑ell ∈ v.asIdeal → ‹IsCrystallineAt r v›  -- gap G1, never stubbed
```

`SourceContract F ell … r : Prop := SourceHypotheses … → ‹r.IsAutomorphic›` (level-free, RACAR
sense — gap, owner `FLT-RACAR-DEF`/`FLT-AUT-GALOIS`). The `‹…›` items are Tier-2 graph gaps: this
block is documentation, not a probe; **no file containing it may be created until the owners land**.

Bridge `selectedGood_to_source_local` (repository → H6/H8 on the generic fibre): consumes
`HasFlatDescentAboveEll` (not `BlueprintSGood.isFlat`) + weight-two data; load-bearing content is
G4 (finite-flat ⇒ crystalline, FL interval), the dominant risk per padic-hodge stage-3. Blocked on
`FLT-MLT-PADIC-HODGE` + `FLT-MLT-COEFFICIENTS`. H5 stays a field-level hypothesis; H1/H2/H7 stay
with RACAR; the level-free ⇒ `IsAutomorphicOfLevel S` step stays in `FLT-MLT` (out of scope).

### Dependency-ordered graph (requirement 7)

```text
GREEN TODAY
  BlueprintSGood (proved vocabulary)            cyclic_base_change (sorried consumer, statement live)
  MLTSourceBoundary residual relations (probe-green)
        │
        ▼
  [P-A] Probes/SelectedGoodRepositoryBoundary.lean  ← FIRST BUILDABLE, standard-trio only
        (SelectedGoodRepository ∙ HasGenericTameRankOneQuotient ∙ HasFlatDescentAboveEll
         ∙ CyclotomicDegreeBound ∙ ComplexEmbeddingData)   [machine-checked this session]
        │
        ├───────────────┬─────────────────────────────┐
        ▼               ▼                             ▼
  [B-1] coefficients   [B-2] weights/sign            [B-3] RACAR witness + H7 +
  bridge — blocked on  bridge — blocked on            attached residual + level-free
  MLTCoefficientData   MLTPadicHodgeWeightData        conclusion — BLOCKED (FLT-RACAR-DEF;
  (not yet landed)     (not yet landed)               prior Opus OBSTRUCTION stands)
        │               │                             │
        └───────┬───────┴──────────────┬──────────────┘
                ▼                      ▼
  [B-4] SourceHypotheses/SourceContract freeze        [B-5] selectedGood_to_source_local
        (needs B-1 ∧ B-2 ∧ B-3)                             (needs B-1 ∧ B-2; G4 dominant risk)
                └──────────────┬───────────────────────────┘
                               ▼
  [OUT OF SCOPE] FLT-MLT terminal: level-free ⇒ IsAutomorphicOfLevel S
  [OPEN, named]  traceOnJ ↔ tame-quotient bridge; HasIntegralModel ↔ HasFlatDescentAboveEll lemma
```

### Counterexamples / false weakenings rejected

1. `IsAutomorphicOfLevel ell … ∅` ≠ H7 — the predicate constrains only `v ∉ S`, `↑p ∉ v.1`
   (away from ℓ, `Automorphic.lean:90`); H7 is at `v | ell` on the RACAR witness.
2. `IsAutomorphicOfLevel S` ≠ the level-free source conclusion (that identification is the whole
   derived `FLT-MLT` theorem).
3. `BlueprintSGood.isFlat` at the generic fibre ≠ `hρflat` — `IsFlatAt` over the field
   `ℚ_[ell]ᵃˡᵍ` is layer-wrong/near-vacuous; the consumer's flat condition lives on the integral
   model `ρ₀` (machine-demonstrated: Probe 2 requires `HasFlatDescentAboveEll` separately).
4. `traceOnJ = 2` ⇎ tame rank-one quotient — no bridge exists in the repository in either
   direction; a tame quotient gives `trace σ = δ(σ) + (det/δ)(σ)` on inertia, equal to 2 only
   under the specific unipotent shape; conversely trace-2 does not produce an equivariant
   surjection `π` without a representability argument. Both spellings coexist; bridge is a named
   open obligation.
5. H5 (`ell` unramified in `F`) ≠ H6 (`r` crystalline at `v | ell`) ≠ H7 (`π_v` unramified) —
   three distinct at-ℓ facts; crystallinity is not Galois unramifiedness at ℓ.
6. "unramified in `F`" ≠ "split completely" (SRC-012, rejected); `SL₂(𝔽_p)`-image (SRC-013) too
   strong.
7. H4 irreducibility must be after restriction to `F(ζ_ell)` — dihedral representations are
   irreducible over `F` yet reducible over `F(ζ_ell)`; and it must be stated on `coeff.rhoBar`.
8. Trace equality alone ≠ residual agreement — charpoly + semisimplicity via
   `IsSemisimplifiedResidualModel`; uniqueness is the separate Brauer–Nesbitt node, never assumed.
9. Fontaine–Laffaille interval is `Set.Icc a (a + (ell:ℤ) - 2)` with one global `a` — a
   per-embedding or diameter-style interval is not source-exact (stage-2 finding); `2 < ell` is
   load-bearing for `{-1, 0} ⊆ Icc`.
10. Sign regression: at `rho` (det = ε, `HT(ε) = −1`) weights are `{-1, 0}`; the dual carries
    `{0, 1}`; stating the boundary at the dual with `{-1, 0}` (or at `rho` with `{0, 1}`) is a
    soundness bug, guarded by the future G7 weight-sum/determinant theorem.
11. Two residual models may differ: distinct stable lattices in the same generic representation
    can have non-isomorphic non-semisimple reductions (Ribet) — hence exactly one
    `CoefficientData` owner shared by H2 and H4.
12. `∃ ι` ≠ carrying `ι` — an existential complex embedding lets two hypotheses use different
    identifications; `ι` is data.
13. Universe drift: restating the flat existential with `R V₀ : Type*` or `finrank` instead of
    `Module.rank` breaks definitional slot-exactness with the consumer.

### Stop-losses

- **S1 (syntax/structure)**: if `: Prop extends BlueprintSGood` misbehaves in the persisted build
  (parent projection or instance-argument issues), fall back to a flat structure repeating the four
  blueprint fields + `supportAwayEll`, with a `rfl`-level equivalence lemma to `BlueprintSGood`.
  Budget: half a day; no design change.
- **S2 (consumer drift)**: the consumer-exactness `example` is the tripwire — if
  `cyclic_base_change`'s signature changes upstream, repair the boundary to match the consumer,
  never the reverse; re-run the exactness probe before any re-freeze.
- **S3 (RACAR)**: `FLT-RACAR-DEF` remains BLOCKED (prior Opus OBSTRUCTION). No stub, no
  placeholder `Prop`, no axiom for the witness/attached/level-free vocabulary. `SourceHypotheses`
  stays documentation until it unblocks. If unblocking stalls beyond the programme window,
  escalate to re-decomposition of `automorphic-galois` — do not route around it here.
- **S4 (vocabulary duplication)**: when `MLTCoefficientData`/`MLTPadicHodgeWeightData` land,
  `SourceHypotheses` spellings track those files exactly; if names shift, this design's B-4 block
  is re-frozen — never fork a second coefficient or weight vocabulary in the MLT packet.
- **S5 (axiom policy)**: acceptance for P-A is `lake build FLTMethodology` green plus
  `#print axioms` = exactly `[propext, Classical.choice, Quot.sound]` for all five declarations;
  any `sorryAx` or new axiom in a persisted declaration aborts the unit. `FLT`/
  `FermatsLastTheorem` roots are untouched (probe library is not imported by them,
  `lakefile.toml:46-48`).
- **S6 (no state promotion)**: `source-design.ndjson` rows for `modularity-lifting` remain
  untouched by this design; `lean_signature` may flip only after P-A lands green **and** the
  mandatory GPT-5.6 xhigh review of this stage passes.

### Verification (for the later, build-enabled task — not this read-only turn)

1. Create `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean` exactly as in P-A; register
   the import in `FLTMethodology.lean`.
2. `lake build FLTMethodology`; then `lake env lean` the probe file and confirm the five
   standard-trio `#print axioms` lines (authoritative per `methodology/FROZEN-BASELINE.md`).
3. Re-run the consumer-exactness elaboration (temp file or quarantined example) and confirm exit 0.
4. `rg`-gate: no `sorry`/`sorryAx`/`axiom` introduced under `FLT/` or `FermatsLastTheorem`;
   `git status` clean except the two intended files.

## Typed Fable decision

`DESIGN-VIABLE` — the repaired boundary is consumer-exact by machine check, the first buildable
probe is green with the standard trio, every remaining hypothesis has a named owner, and every
blocked bridge is blocked on a named unlanded unit rather than on a design defect. `KEEP` at
difficulty 10 remains correct for the packet: the RACAR obstruction and the G4 flat⇒crystalline
node still gate everything downstream of P-A.
