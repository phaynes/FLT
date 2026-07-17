# Stage 6 — Fable 5 coefficient-boundary repair (read-only design)

## Context

Stage 5 (GPT-5.6 xhigh) returned REVISE against the Stage-4 synthesis of `FLT-MLT-COEFFICIENTS`,
identifying six substantive deltas: the dropped generic-closure embedding/tower still needed by
`cyclic_base_change` and `mem_isCompatible`; Type-0-pinned `GroupContract` instantiation;
`extends`-form `CoefficientData`; the unsynthesizable residue `IsLocalHom` adapter required by
`lifts`; preservation of the same-`O` two-lattice charpoly route with cross-`O` left open; and an
incorrect consumer ledger in Stage 4. This Stage-6 pass repairs exactly those deltas, re-runs all
elaboration and `#print axioms` checks in temporary probes outside the repository, and freezes the
`MLTCoefficientData` probe signatures. Nothing in the repository, task state, graph, or Lean
sources was edited; `FLT-MLT-COEFFICIENTS` is not promoted.

**Verdict: DESIGN-VIABLE.**

Environment: Lean `4.32.0-rc1`, Mathlib `a3364faec42918fcd84a03a255b50570129f9ead`.
Review started at checkout `04ba34e`; the branch advanced to `eeac7e9` during the pass
(concurrent Fontaine-Odlyzko work); `git diff --stat 04ba34e..eeac7e9` over every reviewed file
(`FLT/GaloisRepresentation/**`, `FLT/Deformations/**`, `MLTSourceBoundary.lean`,
`BrauerNesbittBoundary.lean`, coefficients stage docs) is empty.

Probes: `/tmp/flt-stage6/probe3.lean` (main, 0 errors), `probe4.lean` (closure descent, 0 errors),
`probe5.lean` (expected-failure evidence), `probe6.lean` (ledger), elaborated with
`lake env lean` from the repo root.

## Delta resolutions (vs Stage 5's six items)

1. **Generic-closure tower: explicitly replaced — and then discharged.** The tower is not put
   back into the structure headers (Stage 4 was right that the *data* never uses it); it becomes
   an explicit wrapper `GenericClosureTower p O E` bundling
   `[Algebra O ℚ̄_p] [Algebra E ℚ̄_p] [IsScalarTower O E ℚ̄_p] [ContinuousSMul O ℚ̄_p]
   [ContinuousSMul E ℚ̄_p]` as instance fields, plus the consumer-shaped predicate
   `DescendsToClosure` and def `closureModel`. Beyond Stage 5's ask, the descent is now **proved**:
   `exists_closure_descent` (below) produces the exact existential
   `∃ rc, (rho0.baseChange C).conj rc = rho.baseChange C` consumed by `cyclic_base_change.hρflat`
   and `mem_isCompatible`, kernel-clean, from `StableLatticeData` alone.
2. **Universes generalized.** `GroupContract` was already universe-polymorphic; the wiring now
   consumes `GroupContract.{uO, uF, uW1, uW2}` with `Wbar₁ : Type uW1`, `Wbar₂ : Type uW2`
   arbitrary (probe-verified; the Stage-3 `{uO, uF, 0, 0}` specialization is gone).
3. **`CoefficientData extends StableLatticeData`** confirmed: elaborates, gives
   `toStableLatticeData`, audits to the trio. (Requires `set_option linter.checkUnivs false` for a
   benign uV01/uW1-only-occur-together lint on the result sort.)
4. **Residue adapter named, not proved.** `ResidueLocalHomAdapter` / `CoefficientGlueContract`
   are open `Prop` definitions. Probe evidence: `infer_instance` fails on
   `IsLocalHom (algebraMap ℤ_[p] (ResidueField O))` under the full bundle context (Stage 5's claim
   confirmed) — while `IsNoetherianRing O` **is** instance-derivable from DVR (PID ⟹ Noetherian),
   so T-A2 sharpens to {finite residue field, adic completeness, residue local-hom}.
5. **Same-`O` charpoly route preserved** (`charpoly_baseChange_eq_of_generic`,
   `residual_charpoly_eq_of_two_integral_models`), proved at fully general module universes;
   cross-`O` comparison stays open as T-IND-CLOSURE.
6. **Ledger re-verified** (see below); Stage 5's table reproduced exactly.

## Frozen probe signatures (`FLTMethodology/Probes/MLTCoefficientData.lean`, when authorized)

All elaborated in `/tmp/flt-stage6/probe3.lean`/`probe4.lean`; every declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`.

Shared explicit context (Stage-3 context minus the generic-closure binders, which move to the
tower wrapper):

```lean
(p : ℕ) [Fact p.Prime] (hp : 2 < p)
(O : Type uO) {F : Type uF} {E : Type uE} {V : Type uV}
[Field F] [NumberField F]
[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
[Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
[TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
[IsNoetherianRing O] [Finite (ResidueField O)]          -- CoefficientData layer only
[IsAdicComplete (maximalIdeal O) O]                     -- CoefficientData layer only
[Field E] [Algebra O E] [IsFractionRing O E]
[TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
[IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
[TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]  -- CoefficientData layer
[DiscreteTopology (ResidueField O)] [ContinuousSMul O (ResidueField O)]   -- CoefficientData layer
[AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
(hV : Module.rank E V = 2) (rho : GaloisRep F E V)
```

Units (universe parameter order is the `universe uO uF uE uV uV01 uV02 uW1 uW2` command order):

```lean
structure StableLatticeData (p hp O … hV rho) where          -- U1; universes {uO,uF,uE,uV,uV01}
  V0 : Type uV01
  [addCommGroupV0 : AddCommGroup V0] [moduleV0 : Module O V0]
  [finiteV0 : Module.Finite O V0] [freeV0 : Module.Free O V0]
  rankV0 : Module.rank O V0 = 2
  rho0 : GaloisRep F O V0
  r0 : E ⊗[O] V0 ≃ₗ[E] V
  compat : (rho0.baseChange E).conj r0 = rho

structure CoefficientData (…) extends
    StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho where   -- U2
  Wbar : Type uW1
  [addCommGroupWbar : AddCommGroup Wbar] [moduleWbar : Module (ResidueField O) Wbar]
  [finiteWbar : Module.Finite (ResidueField O) Wbar] [freeWbar : Module.Free (ResidueField O) Wbar]
  rhobar : GaloisRep F (ResidueField O) Wbar
  isSemisimplifiedResidualModel : IsSemisimplifiedResidualModel rho0 rhobar

structure GenericClosureTower (p : ℕ) [Fact p.Prime] (O : Type uO) (E : Type uE)
    [CommRing O] [TopologicalSpace O] [Field E] [TopologicalSpace E] [Algebra O E] where
  [algebraO : Algebra O (AlgebraicClosure ℚ_[p])]
  [algebraE : Algebra E (AlgebraicClosure ℚ_[p])]
  [tower : IsScalarTower O E (AlgebraicClosure ℚ_[p])]
  [contO : ContinuousSMul O (AlgebraicClosure ℚ_[p])]
  [contE : ContinuousSMul E (AlgebraicClosure ℚ_[p])]

def HasStableLattice : Prop :=                                -- A1'
  Nonempty (StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho)

def HasSemisimplifiedReduction (D : StableLatticeData …) : Prop :=   -- A3'
  ∃ (Wbar : Type uW1) (_ : AddCommGroup Wbar) (_ : Module (ResidueField O) Wbar)
    (_ : Module.Finite (ResidueField O) Wbar) (_ : Module.Free (ResidueField O) Wbar)
    (rhobar : GaloisRep F (ResidueField O) Wbar),
    IsSemisimplifiedResidualModel D.rho0 rhobar

def DescendsToClosure (D : StableLatticeData …) (T : GenericClosureTower p O E)
    {Vc} […] (rhoc : GaloisRep F (AlgebraicClosure ℚ_[p]) Vc) : Prop :=
  letI := T.algebraO; letI := T.contO
  ∃ rc : (AlgebraicClosure ℚ_[p]) ⊗[O] D.V0 ≃ₗ[AlgebraicClosure ℚ_[p]] Vc,
    (D.rho0.baseChange (AlgebraicClosure ℚ_[p])).conj rc = rhoc

noncomputable def closureModel [Algebra O ℚ̄_p] [ContinuousSMul O ℚ̄_p]
    (D : StableLatticeData …) : GaloisRep F ℚ̄_p (ℚ̄_p ⊗[O] D.V0) :=
  D.rho0.baseChange _

-- residual-closure comparison, embeddings as data (U3); the residual closure carries scoped
-- discrete-topology instances (⊥, ⟨rfl⟩); kbar must be pinned: `(kbar := AlgebraicClosure (ZMod p))`
def AgreeInResidualClosure (p) … (rhobar1 : GaloisRep F k1 W1) (rhobar2 : GaloisRep F k2 W2)
    (f1 : k1 →+* AlgebraicClosure (ZMod p)) (f2 : k2 →+* AlgebraicClosure (ZMod p)) : Prop :=
  letI := f1.toAlgebra; letI := f2.toAlgebra
  haveI : ContinuousSMul k1 _ := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousSMul k2 _ := ⟨continuous_of_discreteTopology⟩
  ResidualModelsAgreeAfterExtension (kbar := AlgebraicClosure (ZMod p)) rhobar1 rhobar2

def SemisimpleAscendsToResidualClosureContract : Prop := …     -- M4, open contract

theorem galoisRep_baseChange_apply … :
    rho.baseChange B σ = LinearMap.baseChange B (rho σ) := rfl

theorem galoisRep_baseChange_baseChange (rho0 : GaloisRep F O V0) :   -- proved (probe4)
    (rho0.baseChange E).baseChange C =
      (rho0.baseChange C).conj (AlgebraTensorModule.cancelBaseChange O E C C V0).symm

theorem galoisRep_baseChange_conj (rho' : GaloisRep F E W0) (e : W0 ≃ₗ[E] V) :  -- proved
    (rho'.conj e).baseChange C = (rho'.baseChange C).conj (e.baseChange (A := C))

theorem exists_closure_descent (rho0 …) (rho …) (r0 …)          -- proved; consumer-exact shape
    (hcompat : (rho0.baseChange E).conj r0 = rho) :
    ∃ rc : C ⊗[O] V0 ≃ₗ[C] C ⊗[E] V, (rho0.baseChange C).conj rc = rho.baseChange C

theorem charpoly_baseChange_eq_of_generic                       -- L1a (same O, two lattices)
    (D1 : StableLatticeData.{…,uV01} …) (D2 : StableLatticeData.{…,uV02} …) (σ) :
    (D1.rho0 σ).charpoly = (D2.rho0 σ).charpoly
  -- proof: DFunLike.congr_fun compat, GaloisRep.conj_apply, LinearEquiv.charpoly_conj,
  --        galoisRep_baseChange_apply, LinearMap.charpoly_baseChange,
  --        Polynomial.map_injective (IsFractionRing.injective O E)

theorem residual_charpoly_eq_of_two_integral_models             -- L1b
    (D1 : CoefficientData.{…,uV01,uW1} …) (D2 : CoefficientData.{…,uV02,uW2} …) (σ) :
    (D1.rhobar σ).charpoly = (D2.rhobar σ).charpoly

theorem CoefficientData.finrank_wbar_eq_two (D : CoefficientData …) :
    Module.finrank (ResidueField O) D.Wbar = 2                  -- via residualModel_finrank_eq_two

def LatticeIndependent : Prop :=                                -- U4
  ∀ (D1 : CoefficientData.{uO,uF,uE,uV,uV01,uW1} …) (D2 : CoefficientData.{…,uV02,uW2} …),
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar
  -- explicit instantiation: LatticeIndependent.{uO, uF, uE, uV, uV01, uV02, uW1, uW2}

theorem latticeIndependent_of_groupContract                     -- A4', universe-general
    (hBN : GroupContract.{uO, uF, uW1, uW2}) (D1 …) (D2 …) :
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar

theorem latticeIndependent_of_groupContract'                    -- A4' bundle form
    (hBN : GroupContract.{uO, uF, uW1, uW2}) :
    LatticeIndependent.{uO, uF, uE, uV, uV01, uV02, uW1, uW2} p hp O hV rho

def ResidueLocalHomAdapter [Algebra ℤ_[p] (ResidueField O)]
    [IsScalarTower ℤ_[p] O (ResidueField O)] : Prop :=          -- T-A2a, open
  IsLocalHom (algebraMap ℤ_[p] (ResidueField O))

def CoefficientGlueContract […] : Prop :=                       -- T-A2, open
  IsNoetherianRing O ∧ Finite (ResidueField O) ∧
    IsAdicComplete (maximalIdeal O) O ∧ IsLocalHom (algebraMap ℤ_[p] (ResidueField O))
```

Elaboration hazards found and fixed (record for the production slice):
- `rw [← D.compat]` is ill-typed (motive abstracts `rho`, on which `D`'s type depends); use
  `DFunLike.congr_fun D.compat σ` and rewrite the *applied* term.
- `ResidualModelsAgreeAfterExtension`'s `kbar` is implicit and undetermined by its arguments —
  must be pinned by name or the instance search sticks.
- `closureModel`'s result type needs the tower instances *in the signature* (instance binders),
  not `letI` in the body.
- `Nonempty (StableLatticeData …)` and the `extends` clause require explicit universe
  applications or the declaration retains universe metavariables.
- The conj-commutation lemma needs `W0` at its own universe or unification forces
  `uV = max uE uV0`.

## Dependency order

```
MLTSourceBoundary + BrauerNesbittBoundary (built, audited)
  → U1 StableLatticeData → U2 CoefficientData (extends)
  → GenericClosureTower → closureModel / DescendsToClosure
  → galoisRep_baseChange_apply → galoisRep_baseChange_baseChange
  → galoisRep_baseChange_conj → exists_closure_descent      (closure boundary DISCHARGED)
  → L1a → L1b → finrank_wbar_eq_two
  → U3 AgreeInResidualClosure ; M4 contract
  → U4 LatticeIndependent → A4' (pointwise, bundle)
  → A1' HasStableLattice ; A3' HasSemisimplifiedReduction
  → ResidueLocalHomAdapter / CoefficientGlueContract (open Props)
  ⇢ open providers: T-A2 → T-A1 → T-A3 → M4 → BN → T-IND-CLOSURE
  ⇢ consumers: cyclic_base_change, mem_isCompatible, lifts, deformation stack
```

Note: `cyclic_base_change` quantifies its integral witness at `Type 0` (`R V₀ : Type`); the
bundles are universe-polymorphic and instantiate at `.{0, …}` — no obstruction.

## Probe evidence

- `probe3.lean` (main): **0 errors**; 18/18 proposed declarations audit to exactly
  `[propext, Classical.choice, Quot.sound]` (StableLatticeData, CoefficientData,
  GenericClosureTower, AgreeInResidualClosure, SemisimpleAscendsToResidualClosureContract,
  galoisRep_baseChange_apply, HasStableLattice, HasSemisimplifiedReduction, DescendsToClosure,
  closureModel, charpoly_baseChange_eq_of_generic, residual_charpoly_eq_of_two_integral_models,
  CoefficientData.finrank_wbar_eq_two, LatticeIndependent, latticeIndependent_of_groupContract,
  latticeIndependent_of_groupContract', ResidueLocalHomAdapter, CoefficientGlueContract).
- `probe4.lean`: **0 errors**; galoisRep_baseChange_baseChange, galoisRep_baseChange_conj,
  exists_closure_descent — all exactly the trio.
- `probe5.lean`: `infer_instance` **fails** on `IsLocalHom (algebraMap ℤ_[p] (ResidueField O))`
  under the full bundle context (line 13, `lean.synthInstanceFailed`) and **succeeds** on
  `IsNoetherianRing O`.
- `probe6.lean` + probe3 footer — live-consumer ledger:

  | Declaration | Relationship | Axioms (re-audited) |
  |---|---|---|
  | `GaloisRep.IsAutomorphicOfLevel` (Automorphic.lean:70) | generic coefficient side | trio |
  | `cyclic_base_change` (Automorphic.lean:137) | integral model + closure tower via `hρflat` | trio + `sorryAx` |
  | `GaloisRepresentation.IsHardlyRamified.mem_isCompatible` (Family.lean:37) | integral/closure consumer | trio + `sorryAx` |
  | `GaloisRepresentation.IsHardlyRamified.lifts` (Lift.lean:37) | residual→integral; needs `IsLocalHom (algebraMap ℤ_[p] k)` | trio + `sorryAx` |
  | `Deformation.ProartinianCat.self` (Categories.lean:184) | complete-Noetherian-local view (T-A2) | trio |
  | `Deformation.isCorepresentable_narrowSLiftFunctor` | representability behind `self` | trio + `sorryAx` |

## Still-open mathematical providers

| ID | Statement | Status |
|---|---|---|
| T-A1 | stable lattice exists for every continuous rank-two `rho` (`HasStableLattice`) | open theorem |
| T-A2 | `Finite (ResidueField O)`, `IsAdicComplete`, residue `IsLocalHom` from minimal DVR/finite-free hypotheses (`IsNoetherianRing` already instance-derivable) | open glue |
| T-A3 | semisimplified residual model exists (`HasSemisimplifiedReduction`) | open theorem |
| M4 | semisimplicity ascent finite `k` → residual closure | open contract |
| BN | `GroupContract` (or reviewed branches) | open, `FLT-BRAUER-NESBITT`; consumed only as hypothesis |
| T-IND-CLOSURE | cross-`O` residual comparison through `AgreeInResidualClosure` | open |

## First residual Lean goal

In dependency order, the first goal not closed by any banked declaration or instance
(T-A2a, blocking `lifts` instantiation at `k := ResidueField O`):

```
⊢ IsLocalHom (algebraMap ℤ_[p] (IsLocalRing.ResidueField O))
```

under `[CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
[Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O] [Algebra ℤ_[p] (ResidueField O)]
[IsScalarTower ℤ_[p] O (ResidueField O)]` — mathematically true (p lands in the maximal ideal
because `O` is module-finite over `ℤ_[p]`), but requires a real argument, not synthesis.

## Verification / next probe unit

When (and only when) a later stage authorizes writing to the repository: create
`FLTMethodology/Probes/MLTCoefficientData.lean` with exactly the declarations above plus
`#check`/`#print axioms` footers, register in `FLTMethodology.lean`, and gate with
`lake build FLTMethodology.Probes.MLTCoefficientData`; acceptance = every declaration exactly
`[propext, Classical.choice, Quot.sound]`. Keep unregistered until the typed additional review.
This stage performed no such write and does not promote `FLT-MLT-COEFFICIENTS`.
