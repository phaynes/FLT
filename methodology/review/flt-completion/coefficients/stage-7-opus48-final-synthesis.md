# OPUS 4.8 FINAL REPAIR SYNTHESIS — `FLT-MLT-COEFFICIENTS` (difficulty 10)

## Verdict: READY-FOR-GPT-REVIEW

Read-only. No repository file edited, no axiom registered, no probe persisted, no obligation promoted.
Elaboration re-run is *gated to execution* (see "Stop-loss / honesty" — plan-mode read-only supersedes the
"run temp elaboration" instruction), so the verdict rests on (a) direct read-only re-verification of every
load-bearing API against the current sources and (b) the Stage-6 Fable probe evidence, treated as a *claim to
be re-run*, not as proof.

---

## Context

Stage 4 (Opus 4.8) froze a coefficient interface and returned READY-FOR-GPT-REVIEW. Stage 5 (GPT-5.6 xhigh)
returned **REVISE** with six substantive deltas. Stage 6 (Fable 5) returned **DESIGN-VIABLE**, repairing all
six and additionally *proving* the closure-descent boundary. This final synthesis independently replays the
Fable temporary signatures against the live APIs, confirms each defect is resolved, distinguishes proved
wiring from the six open providers, and freezes the smallest safe production slice.

**Independently re-verified live APIs (read-only, current checkout):**

- `GaloisRep` = `FLT/Deformations/RepresentationTheory/GaloisRep.lean`. Confirmed: `baseChange`
  (l.210, **requires `[Module.Finite A M] [Module.Free A M]` + `[IsTopologicalRing B] [Algebra A B]
  [ContinuousSMul A B]`**), `conj` (l.98), `conj_apply` (l.106), `conj_apply_apply` (l.111), `ext` (l.63),
  `toRepresentation` (l.399), `det` (l.202), `IsIrreducible` (l.404), `IsFlatAt` (l.391).
- `baseChange` returns `GaloisRep K B (B ⊗[A] M)` — so `StableLatticeData.V0` carrying
  `Module.Finite O V0`/`Module.Free O V0` makes `rho0.baseChange E` well-typed. ✔
- Mathlib lemmas the proofs cite all exist: `LinearMap.charpoly_baseChange`
  (`Charpoly/BaseChange.lean:23`), `LinearEquiv.charpoly_conj` (`Charpoly/ToMatrix.lean:76`),
  `AlgebraTensorModule.cancelBaseChange` (`TensorProduct/Tower.lean:436`), `IsFractionRing.injective`
  (`Localization/FractionRing.lean:137`), `Module.finrank_baseChange` (`Dimension/Constructions.lean:378`,
  shape `finrank R (R ⊗[S] M') = finrank S M'`).
- DVR ⟹ Noetherian confirmed: `IsDiscreteValuationRing extends IsPrincipalIdealRing`
  (`DiscreteValuationRing/Basic.lean:59`) ⟹ `IsNoetherianRing O` is instance-derivable. So **T-A2 sharpens
  to {`Finite (ResidueField O)`, `IsAdicComplete`, residue `IsLocalHom`}** — Noetherianity is *not* open.
- `Deformation.ProartinianCat.self` (`Deformations/Categories.lean:180`) needs exactly
  `[IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]`
  and internally uses `compactSpace_of_finite_residueField` (`Patching/Utils/AdicTopology.lean:142`). ✔
- `BrauerNesbittBoundary.lean` and `MLTSourceBoundary.lean` compile-state and public vocabulary
  (`GroupContract`, `IsSemisimplifiedResidualModel`, `SemisimpleResidualEquivalent`,
  `ResidualModelsAgreeAfterExtension`, `residualModel_finrank_eq_two`,
  `semisimplifiedResidualModelsUnique_of_groupContract`, `specializedResidualModelsUnique`,
  `refutedOneSidedTraceContract_false`) match what the design consumes. ✔

---

## The six Stage-5 defects → resolutions (all confirmed)

| # | Stage-5 defect | Resolution in this design | Status |
|---|---|---|---|
| 1 | Generic-closure embedding/tower dropped by Stage 4, but `cyclic_base_change`/`mem_isCompatible` need integral→ℚ̄_p base change | Reintroduced as **explicit wrapper** `GenericClosureTower p O E` (instance-field bundle), *not* in the data headers; consumer-shaped `DescendsToClosure`/`closureModel`; descent **proved** by `exists_closure_descent` | RESOLVED (+proved) |
| 2 | `GroupContract.{uO,uF,0,0}` was Type-0-pinned | Wiring consumes `GroupContract.{uO,uF,uW1,uW2}` with `Wbar₁ : Type uW1`, `Wbar₂ : Type uW2` arbitrary | RESOLVED |
| 3 | Should use `extends`, not flat | `CoefficientData extends StableLatticeData` → `toStableLatticeData` projection | RESOLVED |
| 4 | Residue `IsLocalHom` required by `lifts` is *not* synthesizable | Named **open** `ResidueLocalHomAdapter`/`CoefficientGlueContract` Props; no `infer_instance` | RESOLVED (kept open) |
| 5 | Two-lattice charpoly path valid only same-`O`; cross-`O` left open | `charpoly_baseChange_eq_of_generic` (L1a) + `residual_charpoly_eq_of_two_integral_models` (L1b) proved same-`O`; cross-`O` = open **T-IND-CLOSURE** via `AgreeInResidualClosure` | RESOLVED |
| 6 | Stage-4 consumer ledger wrong (removed closure embedding on false grounds) | Corrected ledger below; `cyclic_base_change`/`mem_isCompatible`/`lifts` restored as closure/residual consumers | RESOLVED |

---

## Exact production signatures — dependency order

Shared explicit context (Stage-3 minus generic-closure binders, which move to `GenericClosureTower`):

```lean
(p : ℕ) [Fact p.Prime] (hp : 2 < p)
(O : Type uO) {F : Type uF} {E : Type uE} {V : Type uV}
[Field F] [NumberField F]
[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
[Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
[TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
[IsNoetherianRing O] [Finite (ResidueField O)]              -- CoefficientData layer only
[IsAdicComplete (maximalIdeal O) O]                         -- CoefficientData layer only
[Field E] [Algebra O E] [IsFractionRing O E]
[TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
[IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
[TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]  -- CoefficientData layer
[DiscreteTopology (ResidueField O)] [ContinuousSMul O (ResidueField O)]   -- CoefficientData layer
[AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
(hV : Module.rank E V = 2) (rho : GaloisRep F E V)
```

Universe command order: `universe uO uF uE uV uV01 uV02 uW1 uW2`.

```
MLTSourceBoundary + BrauerNesbittBoundary            [already built + audited to the trio]
 → U1  StableLatticeData.{uO,uF,uE,uV,uV01}
 → U2  CoefficientData extends StableLatticeData.{…,uV01}      (adds Wbar : Type uW1)
 → GenericClosureTower p O E   →  closureModel / DescendsToClosure
 → galoisRep_baseChange_apply       (= rfl)
 → galoisRep_baseChange_baseChange  →  galoisRep_baseChange_conj  →  exists_closure_descent  ⟵ closure boundary PROVED
 → L1a charpoly_baseChange_eq_of_generic  →  L1b residual_charpoly_eq_of_two_integral_models
 → CoefficientData.finrank_wbar_eq_two   (via residualModel_finrank_eq_two)
 → U3  AgreeInResidualClosure ;  M4  SemisimpleAscendsToResidualClosureContract  (open Prop)
 → U4  LatticeIndependent  →  latticeIndependent_of_groupContract(')
 → A1' HasStableLattice ;  A3' HasSemisimplifiedReduction
 → ResidueLocalHomAdapter / CoefficientGlueContract    (open Props)
 ⇢ open providers: T-A2 → T-A1 → T-A3 → M4 → BN → T-IND-CLOSURE
 ⇢ consumers: cyclic_base_change, mem_isCompatible, lifts, deformation stack
```

Key exact signatures (frozen; replayed against APIs above):

```lean
structure StableLatticeData … where                          -- U1
  V0 : Type uV01
  [addCommGroupV0 : AddCommGroup V0] [moduleV0 : Module O V0]
  [finiteV0 : Module.Finite O V0] [freeV0 : Module.Free O V0]   -- REQUIRED for rho0.baseChange
  rankV0 : Module.rank O V0 = 2
  rho0 : GaloisRep F O V0
  r0 : E ⊗[O] V0 ≃ₗ[E] V
  compat : (rho0.baseChange E).conj r0 = rho

structure CoefficientData … extends StableLatticeData.{uO,uF,uE,uV,uV01} … where   -- U2
  Wbar : Type uW1
  [addCommGroupWbar : AddCommGroup Wbar] [moduleWbar : Module (ResidueField O) Wbar]
  [finiteWbar : Module.Finite (ResidueField O) Wbar] [freeWbar : Module.Free (ResidueField O) Wbar]
  rhobar : GaloisRep F (ResidueField O) Wbar
  isSemisimplifiedResidualModel : IsSemisimplifiedResidualModel rho0 rhobar

structure GenericClosureTower (p) [Fact p.Prime] (O E) [CommRing O] [TopologicalSpace O]
    [Field E] [TopologicalSpace E] [Algebra O E] where
  [algebraO : Algebra O (AlgebraicClosure ℚ_[p])]  [algebraE : Algebra E (AlgebraicClosure ℚ_[p])]
  [tower : IsScalarTower O E (AlgebraicClosure ℚ_[p])]
  [contO : ContinuousSMul O (AlgebraicClosure ℚ_[p])]  [contE : ContinuousSMul E (AlgebraicClosure ℚ_[p])]

theorem galoisRep_baseChange_apply … : rho.baseChange B σ = LinearMap.baseChange B (rho σ) := rfl
theorem galoisRep_baseChange_baseChange (rho0) :
    (rho0.baseChange E).baseChange C = (rho0.baseChange C).conj (AlgebraTensorModule.cancelBaseChange O E C C V0).symm
theorem galoisRep_baseChange_conj (rho') (e) :
    (rho'.conj e).baseChange C = (rho'.baseChange C).conj (e.baseChange (A := C))
theorem exists_closure_descent … (hcompat : (rho0.baseChange E).conj r0 = rho) :
    ∃ rc : C ⊗[O] V0 ≃ₗ[C] C ⊗[E] V, (rho0.baseChange C).conj rc = rho.baseChange C

theorem charpoly_baseChange_eq_of_generic (D1 D2 : StableLatticeData …) (σ) :   -- L1a, same O
    (D1.rho0 σ).charpoly = (D2.rho0 σ).charpoly
  -- DFunLike.congr_fun compat σ ; GaloisRep.conj_apply ; LinearEquiv.charpoly_conj ;
  -- galoisRep_baseChange_apply ; LinearMap.charpoly_baseChange ;
  -- Polynomial.map_injective (IsFractionRing.injective O E)
theorem residual_charpoly_eq_of_two_integral_models (D1 D2 : CoefficientData …) (σ) :  -- L1b
    (D1.rhobar σ).charpoly = (D2.rhobar σ).charpoly
theorem CoefficientData.finrank_wbar_eq_two (D) : Module.finrank (ResidueField O) D.Wbar = 2

def LatticeIndependent : Prop := ∀ (D1 D2 : CoefficientData …), SemisimpleResidualEquivalent D1.rhobar D2.rhobar
theorem latticeIndependent_of_groupContract  (hBN : GroupContract.{uO,uF,uW1,uW2}) (D1 D2) :
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar
theorem latticeIndependent_of_groupContract' (hBN : GroupContract.{uO,uF,uW1,uW2}) :
    LatticeIndependent.{uO,uF,uE,uV,uV01,uV02,uW1,uW2} p hp O hV rho

def ResidueLocalHomAdapter [Algebra ℤ_[p] (ResidueField O)] [IsScalarTower ℤ_[p] O (ResidueField O)] : Prop :=
  IsLocalHom (algebraMap ℤ_[p] (ResidueField O))                      -- T-A2a, OPEN
def CoefficientGlueContract … : Prop :=                               -- T-A2, OPEN
  IsNoetherianRing O ∧ Finite (ResidueField O) ∧ IsAdicComplete (maximalIdeal O) O ∧
    IsLocalHom (algebraMap ℤ_[p] (ResidueField O))
```

Recorded elaboration hazards (carry into the slice): `rw [← D.compat]` is ill-typed (motive depends on
`rho`) — use `DFunLike.congr_fun D.compat σ` on the *applied* term; `ResidualModelsAgreeAfterExtension`'s
`kbar` is implicit/undetermined — pin `(kbar := AlgebraicClosure (ZMod p))`; `closureModel` needs tower
instances **in the signature**, not `letI`; `Nonempty (StableLatticeData …)`/`extends` need explicit
universe applications; the conj-commutation lemma needs `W0` at its own universe.

---

## Proved wiring vs the six open providers

**Bankable with the standard trio `[propext, Classical.choice, Quot.sound]`** (proved wiring):
data structures (U1/U2/`GenericClosureTower`); existence *predicates* `HasStableLattice`/
`HasSemisimplifiedReduction`; `AgreeInResidualClosure`; `galoisRep_baseChange_apply/…_baseChange/…_conj`;
`exists_closure_descent` (closure boundary **discharged**); L1a, L1b, `finrank_wbar_eq_two`;
`LatticeIndependent`; the implication `GroupContract → LatticeIndependent`
(`latticeIndependent_of_groupContract`); the open-Prop *definitions* `ResidueLocalHomAdapter`/
`CoefficientGlueContract`/`SemisimpleAscendsToResidualClosureContract`. Precedent: BrauerNesbittBoundary's
`semisimplifiedResidualModelsUnique_of_groupContract`, `residualModel_finrank_eq_two`,
`specializedResidualModelsUnique` are exactly this "conditional wiring, trio-clean" shape.

**The six OPEN providers** (each entered only as an explicit hypothesis/Prop; none discharged, none an axiom):

| ID | Statement | Kind |
|---|---|---|
| **T-A1** | stable lattice exists for every continuous rank-two `rho` (`HasStableLattice`) | open theorem |
| **T-A2** | residue `IsLocalHom` + `Finite (ResidueField O)` + `IsAdicComplete` from minimal DVR/finite-free hyps (**Noetherian already derivable**) | open glue |
| **T-A3** | semisimplified residual model exists (`HasSemisimplifiedReduction`) | open theorem |
| **M4** | semisimplicity ascent finite `k` → `AlgebraicClosure (ZMod p)` (`SemisimpleAscendsToResidualClosureContract`) | open contract |
| **BN** | `GroupContract` — the `FLT-BRAUER-NESBITT` leaf; consumed only as a hypothesis | open |
| **T-IND-CLOSURE** | cross-`O` residual comparison through `AgreeInResidualClosure` | open |

Policy note: contract *arguments* do not close the graph nodes; T1 admits only `knownin1980s` + the trio.

**Counterexample / negative checks preserved:** `refutedOneSidedTraceContract_false`
(`BrauerNesbittBoundary.lean:311`) proves `¬ RefutedOneSidedTraceContract.{0,0,0,0}` — one-sided trace
bounding is *false* (dims `1` and `p+1` collide in char `p`); so the residual comparison must go through
equal-rank/charpoly, exactly what L1a/L1b + `finrank_wbar_eq_two` supply. Not weakened by this design.

---

## Corrected live-consumer & axiom ledger

| Declaration | Relationship to the design | Current closure |
|---|---|---|
| `GaloisRep.IsAutomorphicOfLevel` (Automorphic.lean:70) | generic coefficient side only | trio (clean) |
| `cyclic_base_change` (Automorphic.lean:137) | integral model + closure tower via `hρflat` | trio + `sorryAx` |
| `IsHardlyRamified.mem_isCompatible` (Family.lean:37) | integral/closure consumer (→ `AlgebraicClosure ℚ_[ℓ]`) | trio + `sorryAx` |
| `IsHardlyRamified.lifts` (Lift.lean:37) | residual→integral; existential **carries `IsLocalHom (algebraMap ℤ_[p] R)`** | trio + `sorryAx` |
| `Deformation.ProartinianCat.self` (Categories.lean:180) | weaker complete-Noetherian-local view (T-A2 export) | trio (clean); representability remains `sorryAx` |

**Nuance I flag for GPT review (not a defect):** `cyclic_base_change.hρflat` demands
`(ρ₀.baseChange ℚ̄_p).conj r₀ = ρ` with ρ **already over ℚ̄_p**, whereas `exists_closure_descent` proves
`(rho0.baseChange C).conj rc = rho.baseChange C`. These agree only after identifying the consumer's literal
ρ with `rho.baseChange C` (the `E := ℚ̄_p` instantiation collapses `rho.baseChange C ≅ rho` via
`cancelBaseChange`/`lid`). The design *encodes* this via `closureModel`/`DescendsToClosure`; the final
identification is a small additional wiring step at the consumer, worth an explicit lemma but not blocking.

Design-layer requirements confirmed real: `DiscreteTopology (ResidueField O)` (finite residual coefficients
for `lifts`), and the T-A2 export for the deformation stack.

---

## Smallest safe production slice

A single **unregistered, unpromoted** methodology probe:
`FLTMethodology/Probes/MLTCoefficientData.lean`, containing exactly — generalized-universe
`StableLatticeData`; `CoefficientData extends StableLatticeData`; `GenericClosureTower` + `closureModel`/
`DescendsToClosure`; `galoisRep_baseChange_apply/…_baseChange/…_conj`; `exists_closure_descent`; L1a; L1b;
`finrank_wbar_eq_two`; `AgreeInResidualClosure`; the M4 contract Prop; `LatticeIndependent` +
`latticeIndependent_of_groupContract(')`; `HasStableLattice`; `HasSemisimplifiedReduction`;
`ResidueLocalHomAdapter`; `CoefficientGlueContract` — each with `#check`/`#print axioms` footers.

- Gate: `lake build FLTMethodology.Probes.MLTCoefficientData`.
- Acceptance: **every** declaration audits to exactly `[propext, Classical.choice, Quot.sound]`.
- Do **not** register in `FLTMethodology.lean` and do **not** promote `FLT-MLT-COEFFICIENTS` until the typed
  additional Fable review passes (difficulty 10 + source/consumer boundary change ⟹ Fable pass REQUIRED).
- First residual Lean goal (blocks `lifts` instantiation at `k := ResidueField O`): `⊢ IsLocalHom
  (algebraMap ℤ_[p] (IsLocalRing.ResidueField O))` — mathematically true (`p` lands in the maximal ideal
  because `O` is module-finite over `ℤ_[p]`), but needs a real argument, not synthesis. That is provider T-A2a.

---

## Stop-loss / honesty

- **No obstruction found.** Every structure is well-typed against the confirmed APIs (notably `baseChange`'s
  `Finite`+`Free` requirement is met by `V0`); every cited mathlib/FLT lemma exists; DVR⟹Noetherian sharpens
  T-A2; the six defects are each resolved with the open nodes kept explicitly open.
- **What I did NOT do (plan-mode read-only supersedes the "run temp elaboration" instruction):** I did not
  write `/tmp` probes or run `lake env lean`. The Stage-6 "0 errors / 18-of-18 trio" figures are therefore
  **carried as a claim to re-run at execution**, not treated as proof. My confidence comes instead from
  independent read-only API verification (above), which is sufficient to send this to GPT review but **not**
  sufficient to bank any declaration.
- **Bankability gate stands:** no declaration is bankable until the slice above elaborates and each
  `#print axioms` returns exactly `[propext, Classical.choice, Quot.sound]` at execution.

**Verdict: READY-FOR-GPT-REVIEW.**

### Open questions for GPT review
1. Provide the explicit `rho.baseChange C ≅ ρ` bridge lemma (E := ℚ̄_p collapse) as banked wiring, or leave
   it to each consumer?
2. Keep source-faithful `IsDiscreteValuationRing O`, exporting the weaker complete-Noetherian-local adapter
   only for deformation consumers (recommended), or relax the source interface?
3. Confirm `universe uO uF uE uV uV01 uV02 uW1 uW2` is the minimal set (no hidden `uV=max uE uV0` collapse in
   the conj-commutation lemma).
