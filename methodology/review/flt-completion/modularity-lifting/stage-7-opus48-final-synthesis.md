# OPUS 4.8 FINAL SYNTHESIS — Modularity-Lifting Source Boundary

## Verdict: `READY-FOR-GPT-REVIEW` (conditioned)

Read-only synthesis of Stage-4 (Opus design), Stage-5 (GPT `REVISE-SUBSTANTIVE`, 4 defects), and
Stage-6 (Fable second repair, `DESIGN-VIABLE`). No repository file, `source-design.ndjson` row,
`proof-graph.ndjson` edge, Lean source, or axiom is edited. Pins: Lean `v4.32.0-rc1`, Mathlib
`a3364fae…`. Every signature below is grounded on a verbatim read of the live tree this turn, not on
the stage docs' paraphrases.

**Not `OBSTRUCTION`:** an exact, machine-grounded design exists and the smallest slice builds today
with the standard trio. **Not `REVISE`:** Stage-6 already repaired all four Stage-5 defects; this
synthesis reconciles Stage-6 against Stage-4/5, checks it against source, and finds no unresolved
defect in the *design*. The remaining blocks (`FLT-MLT-COEFFICIENTS` human-adjudication,
padic-hodge Tier-2 gaps, `FLT-RACAR-DEF` BLOCKED) are documented build-order facts, not design
defects. Compliance point honoured: **closure-form absolute irreducibility is NOT asserted to imply
the repository ∀-extension class** — it is left as the open first residual provider theorem.

---

## Context — why this exists

`FLT-404` owns two objects that must stay separate (`methodology/TRACEABILITY.md:44-46`; no scaffold
may identify either with `IsAutomorphicOfLevel S`):

- **`FLT-SGOOD-SELECTED`** — repository-local proved-vocabulary bundle (home `FLT.ModularityLifting`).
- **`FLT-MLT-SOURCE`** — literal Taylor 2018 Thm 2.1.1 interface, level-free (home
  `FLT.ModularityLifting.Taylor2018.Statement`, decl `…SourceContract`).

Stage-5 GPT raised four substantive defects against Stage-4's gated source design:
(1) H4 used ordinary `GaloisRep.IsIrreducible` (weaker than absolute — the `C₃ ⊂ GL₂(𝔽₂)` split over
`𝔽₄`); (2) `regular`/`fontaineLaffaille` constrained a *free* `weights` never tied to the
representation; (3) H2 residual agreement was same-field, not closure-comparison; (4) the dependency
ledger reversed the live `FLT-MLT-SOURCE → FLT-RESIDUAL-IMAGE` edge. Stage-6 Fable repaired all four
(probe-verified). This synthesis freezes that repair with exact source-grounded signatures.

`source-design.ndjson:9` (modularity-lifting) is `lean_signature:false`,
`dor:"FINAL-REPAIR-SYNTHESIS-RUNNING"`, `next_gate`: *"Complete Opus final synthesis, then obtain
single-lane independent GPT agreement before any probe persistence or graph mutation."* → this
document is that synthesis; a fresh GPT review is the next gate.

---

## Ground truth checked this turn (file:line)

| Fact | Location |
|---|---|
| `cyclic_base_change` ends in `sorry`; `hρflat`/`hρtame`/`hS`/`hp` are the verbatim slots | `FLT/GaloisRepresentation/Automorphic.lean:137-194` |
| `IsAutomorphicOfLevel` `hp = 2 < Module.finrank F (CyclotomicField p F)`; good-prime guard `↑p ∉ v.1 ∧ v ∉ S` | `Automorphic.lean:73,90` |
| `BlueprintSGood = det ∧ isUnramified ∧ traceOnJ=2 ∧ isFlat`, over local `R` | `FLT/ModularityLifting/Conditions.lean:28-42` |
| `GaloisRep`, `.toRepresentation`, `.baseChange`, `.conj`, `.map`, `.toLocal`, `.ker`, `.IsFlatAt`, `.IsIrreducible` present | `FLT/Deformations/RepresentationTheory/GaloisRep.lean:47,399,206,97,75,308,67,389,404` |
| **`GaloisRep.IsCrystallineAt` ABSENT; `GaloisRep.hodgeTateWeightsAt` ABSENT** (real Tier-2 gaps G1/G2) | not in tree — review markdown only |
| `Representation.IsAbsolutelyIrreducible` = ∀-class: `∀ k' : Type u, [Field k'] [Algebra k k'], IsIrreducible (k' ⊗ᵣ' ρ)` | `FLT/Deformations/RepresentationTheory/Irreducible.lean:33-35` (`universe u`, l.21) |
| `Representation.IsIrreducible := IsSimpleOrder (Subrepresentation ρ)`; `Subrepresentation` has a `Lattice` instance | mathlib `RepresentationTheory/Irreducible.lean:30`, `Subrepresentation.lean:31,89` |
| `Representation.baseChange` (`⊗ᵣ'`) | `FLT/Mathlib/RepresentationTheory/Basic.lean:49-58` |
| ∀-class consumer: `[(toRepresentation ρ).IsAbsolutelyIrreducible]`, `G 𝓞 : Type u` | `FLT/Deformations/Representable.lean:34,69` |
| `Slop.OddRep.IsAbsolutelyIrreducible` = closure form at `AlgebraicClosure k` (distinct spelling) | `FLT/Slop/RepresentationTheory/OddAbsIrredSlop.lean:97` |
| Landed weight vocab: `AbstractWeightData`, `IsRegularWeightData`, `HodgeTateWeightsMatch`, `InFontaineLaffailleInterval a`, `EllUnramifiedInIntegers`, `GaloisRepDual`, `weightTwo_fits_iff_two_lt` (`{-1,0}` conv.) | `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean` |
| Landed residual relations: `IsSemisimplifiedResidualModel`, `SemisimpleResidualEquivalent`, `ResidualModelsAgreeAfterExtension (kbar :=…)`, `SemisimplifiedResidualModelsUnique`, `HasIntegralModel` | `FLTMethodology/Probes/MLTSourceBoundary.lean` |
| Coeff (frozen, unlanded): `CoefficientData extends StableLatticeData` with `rhobar : GaloisRep F (ResidueField O) Wbar`; `AgreeInResidualClosure … (f1 f2 : kᵢ →+* AlgebraicClosure (ZMod p))`; first goal `IsLocalHom (algebraMap ℤ_[p] (ResidueField O))` | coefficients stage-6 (`dor: HUMAN-ADJUDICATION-REQUIRED`) |
| `FLTMethodology` is a separate `[[lean_lib]]`, not imported by `FLT`/`FermatsLastTheorem` | `lakefile.toml:26-45`; `FLTMethodology.lean:56-58` |
| Import slot for new probes: between `…PrePsiSeparableOfTorsionCard` (l.35) and `SpecialPreNormEDS` (l.36) | `FLTMethodology.lean` |

---

## Deliverable 1 — Neutral residual-closure vocabulary + first transport contract (req 1)

New defs-only probe `FLTMethodology/Probes/ResidualAbsoluteVocabulary.lean`, namespace
`FLTMethodology.Taylor2018` (eventual home `FLT.ModularityLifting.ResidualVocabulary`). Common closure
= `AlgebraicClosure (ZMod ell)` with scoped discrete instances (`⊥`, `⟨rfl⟩`), matching coefficients
U3. Topology-free: goes through `toRepresentation` + `Representation.baseChange`.

```lean
/-- Absolute irreducibility of a residual rep, tested in the common residual closure via an
explicit embedding `f`. -/
def IsAbsolutelyIrreducibleInResidualClosure
    {K : Type*} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) : Prop :=
  letI := f.toAlgebra
  Representation.IsIrreducible
    (Representation.baseChange (AlgebraicClosure (ZMod ell)) ρbar.toRepresentation)

/-- H4 target: restrict the *same* selected residual model to `F(ζ_ell)` FIRST, then test absolute
irreducibility in the residual closure. (Dihedral reps are irreducible over `F`, reducible over
`F(ζ_ell)` — so restriction must precede the test.) -/
def IsCyclotomicAbsolutelyIrreducibleInResidualClosure
    {F : Type*} [Field F] [NumberField F]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep F k W) : Prop :=
  IsAbsolutelyIrreducibleInResidualClosure ell f
    (ρbar.map (algebraMap F (CyclotomicField ell F)))

/-- PROVIDER CONTRACT (statement only; the first residual goal). Closure-form absolute
irreducibility in the residual closure ⇒ the repository ∀-extension class
`Representation.IsAbsolutelyIrreducible` consumed by `Deformation.Representable`.
NOT proved here. Owner FLT-ABSIRRED-VOCAB. -/
def ClosureImpliesClassAbsIrred
    {K : Type uK} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) : Prop :=
  IsAbsolutelyIrreducibleInResidualClosure ell f ρbar →
    Representation.IsAbsolutelyIrreducible ρbar.toRepresentation   -- universe pin ⇩ see note
```

**Universe-pin obligation (elaboration-checked, not a design guess).** The ∀-class carries the
explicit `universe u` from `Irreducible.lean:21` (`∀ k' : Type u`) plus auto-bound `k/G/W`. Stage-6's
probe hit a metavariable error until the pin was made explicit; the exact tuple
(`Representation.IsAbsolutelyIrreducible.{…}` matching `Deformation.Representable`'s `Type u`) must be
fixed by the elaborator at build time, not asserted here. This is a bounded elaboration item, not a
mathematical claim.

**Why this is only a contract, never an assertion.** The ∀-class quantifies over *every* field
extension `k'` in universe `u`; the closure form tests one algebraic closure. Over a finite residue
field they coincide (Burnside: absolutely irreducible over an algebraically closed field ⇔ image
spans `End`, preserved under any further base change), but that is a *theorem needing a proof*, not a
definitional fact. Per the prompt, it stays `ClosureImpliesClassAbsIrred` = OPEN.

---

## Deliverable 2 — Regularity/Fontaine–Laffaille tied to extracted weights (req 2)

Stage-5 defect 2: `regular`/`fontaineLaffaille` constrained a free `weights` never equated to the
representation's actual Hodge–Tate weights (Stage-6 ProbeD: the free multiset `{3,4}` satisfies both
Stage-4 constraints yet `≠ {-1,0}`). Repair: add a gated field pinning `weights` to `r`'s extracted
weights, owned by padic-hodge Tier-2 (`G2` extraction `hodgeTateWeightsAt` ∘ `G5` place map — both
currently ABSENT, so this field stays `‹gated›`):

```lean
  weightsExtracted : ‹HasHodgeTateWeightData r ι weights›     -- NEW; padic-hodge Tier-2 (G2∘G5)
```

`weights : AbstractWeightData F ell` and its landed constraints `regular : IsRegularWeightData 2
weights`, `fontaineLaffaille : InFontaineLaffailleInterval intervalBase weights` are unchanged;
`weightsExtracted` makes them constrain the *actual* weights, and `weightsMatch : HodgeTateWeightsMatch
weights ‹witnessWeights witness›` (H3) matches them to the RACAR witness. `{-1,0}` at `ρ` /`{0,1}` at
`GaloisRepDual ρ` sign convention preserved (`weightTwo_fits_iff_two_lt`, load-bearing `2 < ell`).

---

## Deliverable 3 — One residual-closure embedding owner for H2 & H4 (req 3)

Single DATA field on `SourceHypotheses`, shared by H2 and H4 (two embeddings would reintroduce the
`∃ι` class of bug — CE-12):

```lean
  embRes : IsLocalRing.ResidueField O →+* AlgebraicClosure (ZMod ell)   -- SINGLE coeff-side owner
```

- **H4** `cycloIrreducible : IsCyclotomicAbsolutelyIrreducibleInResidualClosure ell embRes coeff.rhobar`.
- **H2** `residualAgree : ‹AgreeInResidualClosure ell coeff.rhobar (attachedResidual ι witness) embRes (embAux witness)›`
  — closure-comparison (Stage-5 defect 3), reusing coefficients U3 `AgreeInResidualClosure` which
  delegates to landed `ResidualModelsAgreeAfterExtension (kbar := AlgebraicClosure (ZMod ell))`.

Both reference the **same** `coeff.rhobar` and the **same** `embRes` (Ribet: distinct lattices give
non-isomorphic non-ss reductions — one owner is mandatory). The RACAR-side embedding
`embAux witness : (attachedResidual residue field) →+* AlgebraicClosure (ZMod ell)` is necessarily a
*separate* gap owned by `FLT-RACAR-DEF` (its residue field is not proved identical), which is exactly
why closure-comparison (not same-field equivalence) is required for H2.

### Gated `SourceHypotheses` (documentation — NOT persisted; `‹…›` = gated provider)

```lean
structure SourceHypotheses
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[ell] O]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
      (hV : Module.finrank (AlgebraicClosure ℚ_[ell]) V = 2)
    (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) where
  ι                    : ComplexEmbeddingData ell                       -- data, FLT-MLT-SOURCE
  coeff                : ‹CoefficientData ell hell O hV r›               -- SINGLE coeff owner (COEFFICIENTS)
  embRes               : IsLocalRing.ResidueField O →+* AlgebraicClosure (ZMod ell)  -- SINGLE (H2 & H4)
  weights              : AbstractWeightData F ell                       -- padic-hodge LANDED
  regular              : IsRegularWeightData 2 weights                  -- LANDED
  intervalBase         : ℤ                                              -- one global a
  fontaineLaffaille    : InFontaineLaffailleInterval intervalBase weights   -- H8 LANDED
  weightsExtracted     : ‹HasHodgeTateWeightData r ι weights›           -- R2, Tier-2 (G2∘G5)
  ellUnramifiedInF     : EllUnramifiedInIntegers F ell                  -- H5 LANDED
  witness              : ‹RACAR F›                                      -- H1 BLOCKED
  witnessUnramAboveEll : ∀ v, (↑ell : 𝓞 F) ∈ v.asIdeal → ‹witness.IsUnramifiedAt v›  -- H7
  residualAgree        : ‹AgreeInResidualClosure ell coeff.rhobar (attachedResidual ι witness)
                            embRes (embAux witness)›                    -- H2 closure-comparison (R3)
  weightsMatch         : HodgeTateWeightsMatch weights ‹witnessWeights witness›  -- H3
  cycloIrreducible     : IsCyclotomicAbsolutelyIrreducibleInResidualClosure ell embRes coeff.rhobar  -- H4
  crystallineAbove     : ∀ v, (↑ell : 𝓞 F) ∈ v.asIdeal → ‹r.IsCrystallineAt v›  -- H6 gap G1

def SourceContract … (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) : Prop :=
  SourceHypotheses F ell hell O hV r → ‹r.IsAutomorphic›   -- level-free, gap FLT-RACAR-DEF
```

---

## Deliverable 4 — Corrected acyclic dependency delta (req 4; stated, NOT applied)

Live values (verbatim, `methodology/control/proof-graph.ndjson`):
`FLT-MLT-SOURCE.direct_dependencies = ["FLT-SGOOD-DEF","FLT-AUT-DEF","FLT-MLT-COEFFICIENTS","FLT-MLT-PADIC-HODGE","FLT-RACAR-DEF"]` (l.14);
`FLT-RESIDUAL-IMAGE.direct_dependencies = ["FLT-HR-DEF","FLT-MLT-SOURCE","FLT-AUX-CURVE"]` (l.33);
edge `E-MLT-SOURCE-RESIDUAL-IMAGE` (from `FLT-MLT-SOURCE` to `FLT-RESIDUAL-IMAGE`, l.121). The live
graph therefore has RESIDUAL-IMAGE depending on SOURCE — Stage-4 wrongly implied the reverse.

**Delta (to be applied only at the next authorized mutation stage):**

1. **ADD node** `FLT-ABSIRRED-VOCAB`: `current_state: definition-gap`, `target_stage: T1`,
   `expected_module: FLTMethodology.Probes.ResidualAbsoluteVocabulary` (eventual
   `FLT.ModularityLifting.ResidualVocabulary`), `direct_dependencies: []`,
   `lean_declarations: [IsAbsolutelyIrreducibleInResidualClosure,
   IsCyclotomicAbsolutelyIrreducibleInResidualClosure, ClosureImpliesClassAbsIrred]`.
2. **DELETE edge** `E-MLT-SOURCE-RESIDUAL-IMAGE` (l.121).
3. **ADD edge** `E-ABSIRRED-VOCAB-MLT-SOURCE` (kind `definition`, `FLT-ABSIRRED-VOCAB → FLT-MLT-SOURCE`).
4. **ADD edge** `E-ABSIRRED-VOCAB-RESIDUAL-IMAGE` (kind `definition`, `FLT-ABSIRRED-VOCAB → FLT-RESIDUAL-IMAGE`).
5. `FLT-MLT-SOURCE.direct_dependencies += "FLT-ABSIRRED-VOCAB"`.
6. `FLT-RESIDUAL-IMAGE.direct_dependencies`: **replace** `"FLT-MLT-SOURCE"` **with** `"FLT-ABSIRRED-VOCAB"`
   → `["FLT-HR-DEF","FLT-ABSIRRED-VOCAB","FLT-AUX-CURVE"]`.
7. The concrete residual-image *proof* discharges the source contract's H4 only at the application
   layer `FLT-POTMOD` (edge `E-RESIDUAL-IMAGE-POTMOD`, l.96, already live) — **no** new SOURCE↔RESIDUAL-IMAGE coupling.

**Acyclicity:** `VOCAB(∅) → {SOURCE, RESIDUAL-IMAGE}`; RESIDUAL-IMAGE no longer → SOURCE;
`SOURCE → {MLT (l.79), SGOOD-SELECTED (l.117), AUX-LOCAL-FIELD (l.127)}`;
`RESIDUAL-IMAGE → {TW-PRIMES (l.68), POTMOD (l.96)}`. No cycle. The Stage-4 line "SOURCE consumes
RESIDUAL-IMAGE" is struck. Out of scope (flagged): aux stage-2's HR-DEF↔AUX-CURVE redirection stays
with the FLT-413 packet.

---

## Deliverable 5 — Five trio-clean repository boundary declarations PRESERVED (req 5)

Frozen **verbatim** from Stage-4 P-A, re-audited green in Stage-6 ProbeB and Stage-5 Lean stream (each
`[propext, Classical.choice, Quot.sound]`). Unchanged by this synthesis:

1. `SelectedGoodRepository` — `BlueprintSGood ell rho S` `extends` + `supportAwayEll` (= consumer `hS`).
2. `HasGenericTameRankOneQuotient` — generic-fibre tame rank-one quotient over `ℚ_[ell]ᵃˡᵍ` (= `hρtame`).
3. `HasFlatDescentAboveEll` — integral-model flat existential (= `hρflat`, `R V₀ : Type`,
   `Module.rank R V₀ = 2`, `ρ₀.IsFlatAt v`).
4. `CyclotomicDegreeBound F ell = 2 < Module.finrank F (CyclotomicField ell F)` (= `hp`).
5. `ComplexEmbeddingData ell = (AlgebraicClosure ℚ_[ell]) →+* ℂ` (data).

Three distinct boundaries stay separate (generic tame quotient / integral flat descent /
`BlueprintSGood.traceOnJ`); `traceOnJ ↔ tame-quotient` and `HasIntegralModel ↔ HasFlatDescentAboveEll`
remain **named open** lemmas, not silent identifications.

---

## Deliverable 6 — Definitions/wiring vs still-open provider theorems (req 6)

**Persisted now = definitions & unconditional predicates only** (five units + three residual-closure
defs). `SourceHypotheses`/`SourceContract` stay **documentation** (they term-depend on `‹…›` gated
providers, incl. BLOCKED RACAR). No consumer-exactness `example` is persisted — applying the sorried
`cyclic_base_change` injects `sorryAx` (Stage-6 ProbeC confirmed); it remains an ephemeral `/tmp`
tripwire only.

**Still-open provider theorems (NOT persisted, each named):**

| Provider | Owner | Status |
|---|---|---|
| `ClosureImpliesClassAbsIrred` proof (Burnside/Schur, finite-dim) + embedding-independence lemma | FLT-ABSIRRED-VOCAB | open (first residual goal) |
| `CoefficientData` tower, `GroupContract`/BN, `LatticeIndependent`, `IsLocalHom` adapter | FLT-MLT-COEFFICIENTS | `HUMAN-ADJUDICATION-REQUIRED` |
| G1 `IsCrystallineAt`, G2 `hodgeTateWeightsAt`, `HasHodgeTateWeightData` (G2∘G5), G4 flat⇒crystalline (dominant risk), G6/G7 dual/det transport | FLT-MLT-PADIC-HODGE Tier-2 | gaps |
| `witness`, `attachedResidual` (+ residue field + `embAux`), `witnessWeights`, H7, level-free conclusion | FLT-RACAR-DEF | BLOCKED |

---

## Deliverable 7 — Smallest production slice, gates, first residual goal (req 7)

**Production slice (two defs-only probes, persisted together):**

- `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean` — the five frozen units (verbatim
  Stage-4 P-A). Imports `FLT.GaloisRepresentation.Automorphic`, `FLT.ModularityLifting.Conditions`.
- `FLTMethodology/Probes/ResidualAbsoluteVocabulary.lean` — the three Deliverable-1 defs (predicates;
  no proof obligation). Imports `FLT.Deformations.RepresentationTheory.GaloisRep`,
  `FLT.Mathlib.RepresentationTheory.Basic`, `FLT.Deformations.RepresentationTheory.Irreducible`.

Register both in `FLTMethodology.lean` between l.35 (`…PrePsiSeparableOfTorsionCard`) and l.36
(`…SpecialPreNormEDS`), leaf-alphabetical: `ResidualAbsoluteVocabulary` then
`SelectedGoodRepositoryBoundary`. **Excluded** from the slice: `SourceHypotheses`, `SourceContract`,
`CoefficientData`, any bridge proof, any `example` applying `cyclic_base_change`.

**Build gate:** `lake build FLTMethodology` green. FLT root untouched — `FLTMethodology` is a separate
`[[lean_lib]]` (`lakefile.toml:43-45`) not imported by `FLT`/`FermatsLastTheorem`.

**Axiom gate:** every `#print axioms` across all eight declarations = exactly
`[propext, Classical.choice, Quot.sound]`. Any `sorryAx`/new axiom in a persisted decl aborts the unit
(the two H4-restriction and the transport-contract defs are `Prop`-valued predicates, so they carry no
proof and must audit to the trio).

**First residual Lean goal** (in the later build-enabled stage, once the vocab is persisted):

```lean
⊢ IsAbsolutelyIrreducibleInResidualClosure ell f ρbar →
    Representation.IsAbsolutelyIrreducible.{u} ρbar.toRepresentation
```

i.e. proving `ClosureImpliesClassAbsIrred` — via Burnside over the algebraically closed
`AlgebraicClosure (ZMod ell)` and an order-embedding of `Subrepresentation` lattices under
(faithfully-flat) coefficient extension; needs `Module.Finite k W`. Left OPEN. A structurally trivial
warm-up remains `HasFlatDescentAboveEll ell rho → HasIntegralModel ell rho` (drop the flat conjunct).

---

## Coherence flags (not new disagreements)

1. Three absolute-irreducibility spellings exist: ∀-class (`Deformations/…/Irreducible.lean`),
   `Slop.OddRep` closure form at `AlgebraicClosure k`, and the new residual-closure form at
   `AlgebraicClosure (ZMod ell)`. The vocab node is the single MLT spelling; the ∀-class bridge is the
   open `ClosureImpliesClassAbsIrred`, and the `Slop.OddRep` bridge needs a 1-dim 1-eigenspace (fails
   over `𝔽₂` for the `C₃` counterexample — consistent with Stage-5).
2. `Representation.IsAbsolutelyIrreducible` is FLT-local, not Mathlib.
3. Discrete-topology instances on the closure are declared `local` in two packets (coefficients U3 and
   this vocab file) — one shared home eventually; named coherence point.

## Stop-losses

- **S1** `: Prop extends BlueprintSGood` misbehaving → flat-structure fallback + `rfl` equivalence
  lemma; half-day, no design change.
- **S2** transport-contract universe pin: if the elaborator cannot fix the `.{…}` tuple, keep
  `ClosureImpliesClassAbsIrred` mono-universe (`K k W` shared) and open a named universe-alignment
  lemma; never guess the tuple in a persisted decl.
- **S3** `FLT-RACAR-DEF` stays BLOCKED — no stub/axiom for witness/attached/level-free vocabulary;
  `SourceHypotheses` stays documentation.
- **S4** when coefficients/padic-hodge Tier-2 land, `SourceHypotheses` spellings track them verbatim;
  never fork a second coefficient/weight vocabulary.
- **S5** axiom policy = the trio; any `sorryAx` aborts.
- **S6** no state promotion: `source-design.ndjson:9` and every `proof-graph.ndjson` row untouched
  until the probe lands green **and** the mandatory GPT review passes.

## Verification (later, build-enabled stage — NOT this read-only turn)

1. Create the two probes exactly as above; add both imports to `FLTMethodology.lean` in the l.35–36 gap.
2. `lake build FLTMethodology`; `lake env lean` each probe; confirm all eight `#print axioms` = trio.
3. `/tmp` consumer-exactness tripwire (applies `cyclic_base_change`) → expect
   `[propext, sorryAx, Classical.choice, Quot.sound]`, discard, never persist.
4. `rg`-gate: no `sorry`/`sorryAx`/`axiom` under `FLT/` or `FermatsLastTheorem`; `git status` clean
   except the intended files; `source-design.ndjson` + `proof-graph.ndjson` unchanged.

## Conditions before any promotion (none authorized here)

1. Fresh single-lane GPT-5.6 xhigh review confirms: the two new residual-closure defs + open transport
   contract; `weightsExtracted` tie; single `embRes` for H2/H4; closure-comparison H2; the acyclic
   delta; and the five preserved units.
2. `FLT-MLT-COEFFICIENTS` (human-adjudication), padic-hodge Tier-2, and `FLT-RACAR-DEF` land before the
   gated source block may elaborate.
3. The persisted slice contains only the eight definitions; every `#print axioms` returns the trio.

Until these hold this is a reviewed design candidate — not a completed component, not a state promotion.

---

### FINAL VERDICT: `READY-FOR-GPT-REVIEW`
