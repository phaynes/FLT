# Stage 1 Opus 4.8 primary design — modularity lifting

## Model and transport evidence

- Agent: `opus48-primary-designer-d10`
- Configured model: `claude-opus-4-8`
- Backend transport: Claude CLI through `kg_model_bridge`
- Role: primary design producer
- Design budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `561.514 s`
- Token count: `45,817` input; `302,023` cache-create; `2,413,480` cache-read; `40,553` output; `2,801,873` total including cache, deduplicated over `55` request IDs
- Output characters: `2,549` bridge response; complete plan preserved below
- Baseline HEAD: `1943035a634bcac79fbd57dfa40b6faae88f36d9`
- Claude session: `54eb3473-bd3c-4920-9caf-21986a8d856f`
- Prompt: `methodology/review/flt-completion/modularity-lifting/stage-1-prompt-opus48-primary.md`
- Repository mutation authority: read-only; no model edits permitted
- Verdict: `READY-FOR-GPT-REVIEW`

## Complete primary design

# Opus 4.8 primary early-interface design — modularity-lifting source

- Component: `modularity-lifting`
- Obligations: `FLT-MLT-SOURCE` (→ `FLT.ModularityLifting.Taylor2018.SourceContract`) and
  `FLT-SGOOD-SELECTED` (→ `FLT.ModularityLifting.SelectedGood`)
- Owner work item: `FLT-404`; difficulty `10`; design budget `3600s`
- Selected source: **SRC-016** — R. Taylor, notes by D. Dore & T. Feng, *Automorphy Lifting*
  (2018), **Theorem 2.1.1, printed p. 12**; applications §§2.3.6–2.3.7
- Mode: **read-only / early source-contract only**. Builds remain upstream-gated. This document is a
  mathematical + Lean interface contract; it is not a Lean proof and asserts no closed theorem.

## Context — why this exists

The central review (Fable 5) selected Taylor 2018 Thm 2.1.1 as the modularity-lifting source; the
GPT-5.6 xhigh cross-review (`methodology/review/gpt56xhigh-source-correction.md`) then **corrected**
the encoding: the residual automorphic witness must be unramified at places `v | ell` (an *at-ℓ*
condition), which the repository's away-from-ℓ predicate `IsAutomorphicOfLevel ell … ∅` cannot
express. The `modularity-lifting` row in `methodology/control/source-design.ndjson:9` is `PARTIAL`
with `lean_signature:false`; its `next_gate` is exactly this early-interface design, to be followed
by GPT-5.6 xhigh review. The task: **freeze the literal Thm 2.1.1 interface** (with the corrected
`v | ell` condition, coefficients/lattice, local hypotheses, precise level-free automorphy
conclusion) and **separately define the proved bridge** from repository predicates to that contract.

The programme forbids collapsing three distinct objects (`methodology/TRACEABILITY.md:44-47`):
`BlueprintSGood` (existing, proved, no automorphy conclusion), the Taylor-2018 `SourceContract`
(level-free GL2 automorphy), and `IsAutomorphicOfLevel S` (the *derived* quaternionic theorem,
`FLT-MLT`). "No scaffold may identify either source boundary with `IsAutomorphicOfLevel S`."

---

## Verdict — READY-FOR-GPT-REVIEW (conditioned; elaboration upstream-gated)

The interface design is complete and source-faithful and is ready for the independent GPT-5.6 xhigh
review gate. It deliberately does **not** claim the missing source vocabulary exists or that any
statement elaborates in the verified root today. Honest gating (unchanged from
`methodology/MLT-SOURCE-CONTRACT.md:73-81`): the `SourceContract` shape can be *frozen for review*
now, but can only *elaborate* after three upstream signatures are kernel-green —
`FLT-MLT-COEFFICIENTS`, `FLT-MLT-PADIC-HODGE`, `FLT-RACAR-DEF`.

Load-bearing risk flagged for the reviewer: **`FLT-RACAR-DEF` (component `automorphic-galois`,
`FLT-408`) is `BLOCKED`** (`source-design.ndjson:13`; prior Opus returned `OBSTRUCTION`). Both the
RACAR *witness* (hypotheses 1, 2, 7) and the *conclusion* (level-free automorphy) depend on it, so
those two endpoints remain target shapes, not elaborable predicates. Only `SelectedGood` (Deliverable
B, reusing the proved `BlueprintSGood` surface) elaborates today. This matches how the sibling
`coefficients` and `padic-hodge` designs were dispositioned (READY-FOR-GPT-REVIEW, conditioned).

Verdict is **not** `OBSTRUCTION`: the design work asked for — naming every hypothesis, fixing the
corrected condition, giving the exact shape, ownership, bridge, and build units — is done and
reviewable. The gating is a documented structural fact about *build order*, not a defect in the
interface.

---

## Selected source and the corrected `v | ell` adjudication

Fix a prime `ell > 2`, an identification of the algebraic `ell`-adic and complex closures, a totally
real field `F`, and a regular-algebraic two-dimensional `ell`-adic representation `r` of `Gal(F̄/F)`.
Theorem 2.1.1 requires (verbatim from `methodology/MLT-SOURCE-CONTRACT.md:13-24`):

1. a regular-algebraic cuspidal automorphic representation `π` of `GL₂/F` (RACAR);
2. an isomorphism of the **semisimplified residual** representations attached to `π` and `r`;
3. matching Hodge–Tate weights at every embedding;
4. irreducibility of the residual representation **after restriction to `F(ζ_ell)`**;
5. `ell` **unramified** in `F` (unramified — *not* split completely; this rejects SRC-012);
6. **crystallinity** of `r` at every place above `ell`;
7. **unramifiedness of `π_v` at every place `v | ell`** ← the corrected at-ℓ condition;
8. all Hodge–Tate weights inside a **Fontaine–Laffaille interval of length `ell − 1`**.

Conclusion: `r` is automorphic in the source's **level-free GL₂/RACAR** sense.

**The correction (item 7).** The original encoding tried to force an everywhere-unramified witness
via `IsAutomorphicOfLevel ell … ∅`. `IsAutomorphicOfLevel` constrains only *good* primes `v ∉ S`
with `↑p ∉ v.1` (`FLT/GaloisRepresentation/Automorphic.lean:90`) — i.e. away from `ell`. Item 7 is an
*at-ℓ* condition on `π`; it must be a separate field `∀ v, ↑ell ∈ v.asIdeal → π.IsUnramifiedAt v` on
the RACAR witness. In the notes' two auxiliary-curve applications it is discharged by **good
reduction** at the two selected primes. Item 7 is distinct from item 5 (`ell` unramified in the
*field* `F`) and item 6 (`r` *crystalline* at `v | ell`) — these three at-ℓ facts must not be merged.

---

## Deliverable A — `FLT-MLT-SOURCE`: literal Theorem 2.1.1 interface

Home module: `FLT.ModularityLifting.Taylor2018.Statement`. Two-tier, matching the sibling packets.

### Tier-2 named gaps this contract consumes (not fabricated `Prop`s)

| Gap predicate/object | Owner obligation | State |
|---|---|---|
| coefficient field `L = ℚ_[ell]ᵃˡᵍ`, stable `O`-lattice, semisimplified residual reduction (`CoefficientData`) | `FLT-MLT-COEFFICIENTS` | designed, not green |
| `GaloisRep.IsCrystallineAt`, `hodgeTateWeightsAt`, `HodgeTateWeightsMatch`, `IsRegularWeightData`, `InFontaineLaffailleInterval`, `ell` unramified in `F` | `FLT-MLT-PADIC-HODGE` | designed, not green |
| `RACAR F` witness object, its attached residual rep, `π.IsUnramifiedAt v`, level-free `r.IsAutomorphic` conclusion | `FLT-RACAR-DEF` / `FLT-AUT-GALOIS` | **BLOCKED** |
| residual comparison (`IsSemisimplifiedResidualModel`, charpoly + semisimplicity) | banked in `FLTMethodology/Probes/MLTSourceBoundary.lean` | probe-green (not verified root) |

The residual-comparison probes already exist and audit with the standard trio:
`HasIntegralModel`, `IsSemisimplifiedResidualModel`, `SemisimpleResidualEquivalent`,
`ResidualModelsAgreeAfterExtension`, `SemisimplifiedResidualModelsUnique`
(`FLTMethodology/Probes/MLTSourceBoundary.lean:23-104`). Item 2's isomorphism is
`IsSemisimplifiedResidualModel` composed with `SemisimpleResidualEquivalent`, *not* trace equality
alone (Brauer–Nesbitt is a separate obligation).

### Frozen theorem shape (target; elaborates only after the three upstream signatures are green)

```lean
namespace FLT.ModularityLifting.Taylor2018

open scoped TensorProduct NumberField

/-- The exact hypotheses of Taylor 2018, Theorem 2.1.1, as a data+Prop bundle over a
regular-algebraic 2-dimensional `ell`-adic representation `r` on an algebraic `ell`-adic
coefficient field. Predicates named `‹gap›` are Tier-2 obligations, not defined here. -/
structure SourceHypotheses
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    -- coefficient field L = algebraic closure of ℚ_ell  (FLT-MLT-COEFFICIENTS)
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
      (hV : Module.finrank (AlgebraicClosure ℚ_[ell]) V = 2)
    (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) where
  -- (H0) regular algebraicity of r's weight datum          [gap: FLT-MLT-PADIC-HODGE]
  regularAlgebraic  : ‹IsRegularAlgebraic r›
  -- (H1) a RACAR witness π of GL₂/F                          [gap: FLT-RACAR-DEF]
  witness           : ‹RACAR F›
  -- (H2) semisimplified residual reps of π and r agree       [FLT-MLT-COEFFICIENTS + probe]
  residualAgree     : ‹SemisimplifiedResidualOf r›.AgreesWith ‹attachedResidual witness›
  -- (H3) Hodge–Tate weights match at every embedding         [gap: FLT-MLT-PADIC-HODGE]
  weightsMatch      : ‹HodgeTateWeightsMatch r witness›
  -- (H4) residual irreducibility after restriction to F(ζ_ell)
  cycloIrreducible  : GaloisRep.IsIrreducible
                        ((‹residualReduction r›).map (algebraMap F ‹F adjoin ζ_ell›))
  -- (H5) ell unramified in F                                 [gap: FLT-MLT-PADIC-HODGE]
  ellUnramifiedInF  : ‹IsUnramified ℤ (𝓞 F) ell›
  -- (H6) r crystalline at every v | ell                      [gap: FLT-MLT-PADIC-HODGE]
  crystallineAbove  : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                        ↑ell ∈ v.asIdeal → ‹r.IsCrystallineAt v›
  -- (H7) CORRECTED: π_v unramified at every v | ell          [gap: FLT-RACAR-DEF]
  witnessUnramAboveEll : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                        ↑ell ∈ v.asIdeal → ‹witness.IsUnramifiedAt v›
  -- (H8) all HT weights in a Fontaine–Laffaille interval of length ell − 1
  fontaineLaffaille : ‹InFontaineLaffailleInterval r (ell - 1)›

/-- Taylor 2018, Theorem 2.1.1 — the source contract. Level-free GL₂ automorphy.
The conclusion `r.IsAutomorphic` is the level-free predicate `∃ RACAR π̃, attached(π̃) ≅ r`
[gap: FLT-RACAR-DEF]; it is NOT `IsAutomorphicOfLevel S`. -/
def SourceContract
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
      (hV : Module.finrank (AlgebraicClosure ℚ_[ell]) V = 2)
    (r : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) : Prop :=
  SourceHypotheses F ell hell hV r → ‹r.IsAutomorphic›

end FLT.ModularityLifting.Taylor2018
```

`‹…›` marks a Tier-2 gap object/predicate. The eventual theorem is
`theorem taylor2018_2_1_1 … : SourceContract F ell hell hV r`, proved only after all owners land.
Real, elaborable references used above: `GaloisRep`, `GaloisRep.IsIrreducible`, `GaloisRep.map`,
`AlgebraicClosure ℚ_[ell]`, `Module.finrank`, `HeightOneSpectrum`, `↑ell ∈ v.asIdeal`.

---

## Deliverable B — `FLT-SGOOD-SELECTED`: repository bundle + the proved bridge

Home module: `FLT.ModularityLifting.Conditions` (alongside `BlueprintSGood`). This is the
*repository-local, weight-two* condition bundle selected to match what Thm 2.1.1 needs, plus the
**bridge theorem** whose statement is frozen now and whose proof reduces to named p-adic-Hodge and
coefficient owners. It is distinct from `BlueprintSGood`/`FLT-SGOOD-DEF` (already proved) and must
**not** be identified with `IsAutomorphicOfLevel S`.

### B.1 The selected structure (elaborates now — reuses proved vocabulary)

Uses the source-faithful **tame rank-one quotient** spelling from `cyclic_base_change`
(`FLT/GaloisRepresentation/Automorphic.lean:180-188`), which is stronger/more faithful than
`BlueprintSGood.traceOnJ = 2`:

```lean
namespace FLT.ModularityLifting

/-- Repository weight-two local conditions selected after Taylor 2018: cyclotomic determinant,
unramified outside `S ∪ {ell}`, a tame rank-one quotient character at each `v ∈ S`, and a finite-flat
integral model above `ell`. Carries NO automorphy conclusion and NO crystalline/HT condition; those
are supplied by the bridge (B.2). -/
structure SelectedGood
    {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[ell] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (rho : GaloisRep F R V)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) : Prop where
  det : ∀ g, rho.det g =
    algebraMap ℤ_[ell] R (cyclotomicCharacter (AlgebraicClosure F) ell g.toRingEquiv)
  isUnramified : ∀ v, v ∉ S → ↑ell ∉ v.asIdeal → rho.IsUnramifiedAt v
  tameRankOneQuotient : ∀ w ∈ S, ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π)
    (δ : GaloisRep (w.adicCompletion F) R R),
      localTameAbelianInertiaGroup w ≤ δ.ker ∧
      ∀ g v, π ((rho.toLocal w) g v) = δ g (π v)
  isFlat : ∀ v, ↑ell ∈ v.asIdeal → rho.IsFlatAt v

end FLT.ModularityLifting
```

Every field above uses declarations that exist and are kernel-clean today: `GaloisRep.det`,
`cyclotomicCharacter`, `GaloisRep.IsUnramifiedAt`, `localTameAbelianInertiaGroup`, `GaloisRep.toLocal`,
`GaloisRep.ker`, `GaloisRep.IsFlatAt`. (Design choice for review: keep `traceOnJ = 2` as an
alternative/weaker field, or commit to `tameRankOneQuotient`; the latter is what the derived theorem
`cyclic_base_change` actually uses.)

### B.2 The bridge (statement frozen now; proof reduces to named owners)

This is the "proved bridge from repository predicates to that source contract" the task requires. It
lifts the *repository-local, integral* `SelectedGood ρ₀` conditions to the *source-level* local
hypotheses (H5–H8) on the base-changed `L`-representation `r = ρ₀ ⊗ L`, given the coefficient data.

```lean
/-- Bridge: the repository weight-two `SelectedGood` conditions on an integral model `ρ₀`, together
with coefficient data, supply exactly Taylor 2018's local hypotheses (H5–H8) on `r = ρ₀ ⊗ L`.
The load-bearing content is finite-flat ⇒ crystalline weight-two (FLT-MLT-PADIC-HODGE); this
theorem only ASSEMBLES ownerships and is NOT proved here. -/
theorem selectedGood_to_source_local
    {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    (ell : ℕ) [Fact ell.Prime] (hell : 2 < ell)
    {O : Type*} [CommRing O] [IsLocalRing O] [Algebra ℤ_[ell] O] /- DVR coeff, FLT-MLT-COEFFICIENTS -/
    {V₀ : Type*} [AddCommGroup V₀] [Module O V₀] [Module.Finite O V₀] [Module.Free O V₀]
    (ρ₀ : GaloisRep F O V₀)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hgood : SelectedGood ell ρ₀ S)
    (coeff : ‹CoefficientData ρ₀›) :        -- FLT-MLT-COEFFICIENTS
    -- H5 (ell unramified in F) is field-level input, not derived here;
    -- the bridge delivers H6 (crystalline) and H8 (FL interval) from `isFlat` + weight two:
    (∀ v, ↑ell ∈ v.asIdeal → ‹(coeff.baseChange).IsCrystallineAt v›) ∧
    ‹InFontaineLaffailleInterval coeff.baseChange (ell - 1)› :=
  sorry  -- reduces to `GaloisRep.isCrystalline_of_isFlatAt_weightTwo` (FLT-MLT-PADIC-HODGE)
```

Explicitly *out of scope of this bridge* (kept as separate obligations, not hidden here): item 5
(`ell` unramified in `F`) is a field hypothesis; items 1/2/7 (RACAR witness + at-ℓ unramifiedness)
belong to `FLT-RACAR-DEF`; the level-free ⇒ `IsAutomorphicOfLevel S` step is `FLT-MLT` (separate).

---

## Source-hypothesis ownership

| Thm 2.1.1 hypothesis | Owner obligation |
|---|---|
| RACAR `π` (H1) | `FLT-RACAR-DEF` (BLOCKED) |
| semisimplified residual agreement (H2) | `FLT-MLT-COEFFICIENTS` (+ probe relations) |
| Hodge–Tate weight match (H3) | `FLT-MLT-PADIC-HODGE` |
| residual irreducibility over `F(ζ_ell)` (H4) | `FLT-RESIDUAL-IMAGE` |
| `ell` unramified in `F` (H5) | `FLT-MLT-PADIC-HODGE` |
| crystalline at every `v \| ell` (H6) | `FLT-MLT-PADIC-HODGE` |
| `π_v` unramified at every `v \| ell` (H7, corrected) | `FLT-RACAR-DEF` |
| Fontaine–Laffaille interval, length `ell − 1` (H8) | `FLT-MLT-PADIC-HODGE` |
| level-free automorphy conclusion | `FLT-RACAR-DEF` / `FLT-AUT-GALOIS` |
| `SelectedGood` bundle + `selectedGood_to_source_local` | this obligation, `FLT-SGOOD-SELECTED` |

Downstream consumers (must not be broken): `FLT-MLT-SOURCE` feeds `FLT-MLT`, `FLT-RESIDUAL-IMAGE`,
`FLT-AUX-LOCAL-FIELD`; `FLT-SGOOD-SELECTED` feeds `FLT-DEF-FUNCTOR`, `FLT-LOCAL-GALOIS`,
`FLT-HECKE-ACTION`, `FLT-MLT`.

## Dependency order

```text
FLT-SGOOD-DEF (BlueprintSGood, PROVED)  ─────────────┐
FLT-MLT-COEFFICIENTS (designed, not green) ─┐         │
FLT-MLT-PADIC-HODGE  (designed, not green) ─┤         │
FLT-RACAR-DEF        (BLOCKED)             ─┤         │
                                            │         ▼
     SelectedGood (B.1) ─── elaborates now, reuses proved surface
                                            │
     SourceContract shape (A) ── gated on the three upstream signatures
                                            │
     selectedGood_to_source_local (B.2) ── gated on PADIC-HODGE + COEFFICIENTS
                                            │
     [separate] FLT-MLT : level-free ⇒ IsAutomorphicOfLevel S  (OUT OF SCOPE)
```

## Counterexamples / false-weakenings rejected

1. `IsAutomorphicOfLevel ell … ∅` ≠ H7. `IsAutomorphicOfLevel` constrains only good primes `v ∉ S`,
   `↑p ∉ v.1` (away from ℓ); H7 is at `v | ell`. The corrected, load-bearing separation.
2. `IsAutomorphicOfLevel S` ≠ the level-free conclusion. That is the derived `FLT-MLT` theorem.
3. `GaloisRep.IsFlatAt` ≠ crystalline/HT (H6). Finite-flat is not definitionally crystalline; the
   weight-two bridge is real Raynaud/Fontaine–Laffaille mathematics (`FLT-MLT-PADIC-HODGE`).
4. A generic integral-`O` representation ≠ the source `L`-representation. Stable-lattice choice,
   residual reduction, and semisimplification are explicit obligations, not definitional.
5. H5 (`ell` unramified in `F`) ≠ H6 (crystalline at `v | ell`) ≠ H7 (`π_v` unramified). Three
   distinct at-ℓ facts; merging any two is unsound.
6. "unramified in `F`" (H5) ≠ "split completely" — the latter (SRC-012, Taylor 2006) is a *different,
   rejected* source; likewise `SL₂(F_p)`-image (SRC-013, Gee 2022) is too strong.
7. Residual irreducibility must be **after** restriction to `F(ζ_ell)` (H4). Irreducibility over `F`
   alone is insufficient (dihedral / becomes-reducible-after-restriction counterexamples).
8. Residual agreement (H2) needs full characteristic-polynomial equality + semisimplicity, not trace
   equality alone (Brauer–Nesbitt, a separate obligation) — enforced by `IsSemisimplifiedResidualModel`.
9. Fontaine–Laffaille interval length `ell − 1`: `2 < ell` is load-bearing; a weight-two `{0,1}` set
   must fit; must be `ell − 1` consecutive integers (convention to confirm — see review Q1).
10. `SelectedGood` must not silently include an automorphy or crystalline field; those are bridged,
    not assumed. Keeping `tameRankOneQuotient` (character `δ`) faithful, not just `trace = 2`.

## Signature probes (home: `FLTMethodology/Probes/`, NOT the verified root)

- **P1 — `SelectedGoodSignatureProbe.lean`**: elaborate `SelectedGood` and `#print axioms
  SelectedGood`; must show only `[propext, Classical.choice, Quot.sound]`. Expected green now
  (reuses proved vocabulary). Closes the sole T1 signature sub-gate available today.
- **P2 — `SourceContractShapeProbe.lean`**: elaborate the Tier-1-expressible fields (`det = cyclo`,
  `IsIrreducible` after `.map` to `F(ζ_ell)`, `witnessUnramAboveEll` shape, `↑ell ∈ v.asIdeal`
  guards) against stubbed gap predicates; confirm the *shape* type-checks and `#print axioms`.
  Gated: the gap predicates must be stubbed to run; do NOT promote.
- **P3 — `SelectedGoodBridgeProbe.lean`**: state `selectedGood_to_source_local`'s type with gap
  predicates stubbed; confirm the type elaborates and the `sorry` body isolates exactly the
  flat⇒crystalline reduction. `#print axioms` will show `sorryAx` — this is a *signature* probe, not
  a proof, and stays out of the verified root (`lakefile.toml:41-45`).

## Bounded later build units

1. **BU-1** — `SelectedGood` (B.1) + P1 probe. *Only unit expected to pass a T1 signature gate now.*
2. **BU-2** — register the RACAR witness, `r.IsAutomorphic` conclusion, and H7 predicate as named
   Tier-2 graph gaps blocked on `FLT-RACAR-DEF`; add the `FLT-MLT-PADIC-HODGE → FLT-RACAR-DEF` edge
   the prior OBSTRUCTION requested.
3. **BU-3** — assemble `SourceHypotheses` + `SourceContract` (A) once coefficients, padic-hodge, and
   RACAR signatures are kernel-green; P2 probe promotes to elaboration.
4. **BU-4** — state + prove `selectedGood_to_source_local` (B.2) via
   `GaloisRep.isCrystalline_of_isFlatAt_weightTwo` (from `FLT-MLT-PADIC-HODGE`).
5. **BU-5** — *out of scope here*: `FLT-MLT` level-free ⇒ `IsAutomorphicOfLevel S` (patching, Hecke,
   Jacquet–Langlands, `cyclic_base_change` de-`sorry`-ing).

## Soundness checks retained

- The contract carries no `sorryAx` in any promoted declaration; `SelectedGood` audits with the
  standard trio only; gap-dependent statements stay in `FLTMethodology` (never the verified root).
- Crystalline, Hodge–Tate, Fontaine–Laffaille, RACAR, and the level-free conclusion are gaps, not
  opaque `Prop`s and not admitted theorems in a green module.
- The corrected at-ℓ witness condition (H7) lives on the RACAR witness, never inside an away-from-ℓ
  `IsAutomorphicOfLevel … ∅`.
- The three-way separation (`BlueprintSGood` / `SourceContract` / `IsAutomorphicOfLevel S`) is
  preserved; `SelectedGood ≠ BlueprintSGood` (tame rank-one quotient vs trace-two) is deliberate.

## Questions for independent GPT-5.6 xhigh review

1. Fontaine–Laffaille "length `ell − 1`": `ell − 1` consecutive integers `[a, a+ell−2]`, or diameter?
   (Shared convention with the `padic-hodge` packet.)
2. Coefficient field: commit to `AlgebraicClosure ℚ_[ell]` (repository idiom `ℚ_[p]ᵃˡᵍ`), or a finite
   extension `L/ℚ_[ell]` with a chosen embedding?
3. `SelectedGood`: adopt `tameRankOneQuotient` (character `δ`, per `cyclic_base_change`) as the
   source-faithful field, or retain `traceOnJ = 2`, or carry both?
4. Confirm H4 restriction target is `F(ζ_ell)` and confirm the residual reduction used there is the
   semisimplified one.
5. Confirm the level-free conclusion predicate is `∃ RACAR π̃, attached(π̃) ≅ r`, and that no part of
   it may be discharged by `IsAutomorphicOfLevel`.
6. Confirm the bridge (B.2) may own only H6/H8 (leaving H5 field-level and H1/H2/H7 to RACAR).

## Conditions before promotion

1. GPT-5.6 xhigh review must confirm the corrected `v | ell` condition placement and the
   coefficient/lattice boundary, and settle Q1–Q6.
2. `FLT-MLT-COEFFICIENTS`, `FLT-MLT-PADIC-HODGE`, and `FLT-RACAR-DEF` signatures must be kernel-green
   before `SourceContract` (A) may elaborate; `FLT-RACAR-DEF` is currently BLOCKED.
3. A Wave-0-enabled probe must confirm `SelectedGood` (B.1) elaborates and audits with the standard
   trio; `SourceContract`/bridge probes stay in `FLTMethodology` until their owners land.
4. No promoted green declaration may contain `sorryAx` or an unapproved custom axiom (T1 policy).

Until these hold, this is a reviewed design candidate — not a completed component, and not a
proof-state promotion.

---

## Plan-file note (how this deliverable would be recorded, if approved)

Read-only design; nothing in this repo is edited by producing it. If approved for the programme, the
resulting artifacts (a later, build-enabled task — not this plan-mode turn) would be:

- write `methodology/review/flt-completion/modularity-lifting/stage-1-opus48-primary.md` (this design,
  house format), mirroring the `coefficients`/`padic-hodge` sibling stage-1 packets;
- add the P1/P2/P3 signature probes under `FLTMethodology/Probes/`;
- flip `source-design.ndjson:9` `lean_signature` handling only after P1 is green and review passes;
- leave `FLT-MLT-SOURCE`/`FLT-SGOOD-SELECTED` `current_state:"definition-gap"` until upstream lands.

**Verification (later, gated):** `lake build FLTMethodology` for P1; `lake env lean` the probe files
and read `#print axioms` output (authoritative per `methodology/FROZEN-BASELINE.md`); confirm no new
`sorry`/`sorryAx` enters `FLT`/`FermatsLastTheorem` via the `rg` gating commands.

