# GPT-5.6 xhigh independent review — coefficients

Component: `coefficients / FLT-MLT-COEFFICIENTS`  
Role: independent verifier; read-only  
Verdict: `REFUTED` for the frozen Opus design, not for the Taylor route

The Taylor route is not refuted; the frozen Opus coefficient design is. Its literal signatures fail W00 elaboration, and A1 is false as quantified.

- **A1 is false and ill-typed.** `exists_stableLattice` permits arbitrary finite free `V` but demands a rank-two integral model. The one-dimensional trivial representation is a counterexample. Moreover, the reused `HasIntegralModel` accepts only representations over `AlgebraicClosure ℚ_[p]`, not generic `E` (`FLTMethodology/Probes/MLTSourceBoundary.lean:23`; proposed A1 in the Opus plan).

- **The advertised W00 signature fails on Lean 4.32.0-rc1 / Mathlib `a3364fa`.**
  - `IsDiscreteValuationRing O` requires a separate `[IsDomain O]`; it does not provide one (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:58`).
  - `ρ̄` is not a valid Lean identifier; use `rhoBar`.
  - `ResidueField O` supplies a field, but no topology, `IsTopologicalRing`, or `ContinuousSMul` instances required by `GaloisRep` and `baseChange`.
  - A1's generic-`E` call to the existing scaffold does not elaborate.

- **The coefficient context is silently erased.** Even after repairing those immediate errors, `#check @CoefficientData` omitted `p`, `2 < p`, finite/free over `ℤ_[p]`, `IsFractionRing O E`, completeness, and the scalar tower because they were ambient variables unused by the structure. They must be explicit structure parameters or a reified context.

- **U6 does not contain what it claims.** Its last field is merely `residual`; there is no common algebraic closure, residue-field embedding, scalar-extension comparison, or Brauer-Nesbitt witness. Consequently U6 does not depend on U5/A4 as claimed.

- **A4 is not lattice independence.** `SemisimplifiedResidualModelsUnique` compares two semisimplifications of the same `ρ₀`; it cannot compare reductions of two different stable lattices in the same characteristic-zero representation (`FLTMethodology/Probes/MLTSourceBoundary.lean:89`). The fixed common residual algebraic closure and embeddings remain absent.

- **A2/A3 are not closed.** A2's completeness, Noetherianity, and finite-residue conclusions are absent from the bundle. A3 lacks the residue-field topology and finiteness assumptions needed to construct a continuous `GaloisRep`.

- **The target-stage description is wrong.** Literal `theorem ... := by sorry` creates `sorryAx`; it is not a checked proposition. A1-A4 cannot simply be postponed to T2/T3 because `FLT-MLT-COEFFICIENTS` is in the T1 closure. T1 permits only the visible `knownin1980s` boundary besides the standard trio.

The repaired maximal-ideal-kernel condition, full characteristic-polynomial comparison, semisimplicity requirement, and bundle-plus-Prop strategy remain sound. The existing five scaffold definitions still audit with exactly `[propext, Classical.choice, Quot.sound]`.

**Typed Fable trigger: KEEP.** Difficulty is 10 and the independent review found substantive mathematical and statement-level defects: A1 is false, A4 proves the wrong relation, and the claimed U6 boundary omits its load-bearing comparison data. This is not a mechanical-only correction.

## Next exact signature probe

Probe a data-only bundle with every source condition explicitly bound, no A1/A3 theorem, and ASCII identifiers:

```lean
structure CoefficientDataProbe
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    {F O E V : Type*}
    [Field F] [NumberField F]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
    [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Field E] [Algebra O E] [IsFractionRing O E]
    [TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
    [IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
    [Algebra E (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul E (AlgebraicClosure ℚ_[p])]
    [TopologicalSpace (IsLocalRing.ResidueField O)]
    [IsTopologicalRing (IsLocalRing.ResidueField O)]
    [ContinuousSMul O (IsLocalRing.ResidueField O)]
    [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
    (hV : Module.rank E V = 2) (rho : GaloisRep F E V) where
  V0 : Type
  addCommGroupV0 : AddCommGroup V0
  moduleV0 : Module O V0
  finiteV0 : Module.Finite O V0
  freeV0 : Module.Free O V0
  rank_two : @Module.rank O V0 _ _ moduleV0 = 2
  rho0 : GaloisRep F O V0
  r0 : E ⊗[O] V0 ≃ₗ[E] V
  compat : (rho0.baseChange E).conj r0 = rho
  W : Type
  addCommGroupW : AddCommGroup W
  moduleW : Module (IsLocalRing.ResidueField O) W
  finiteW : Module.Finite (IsLocalRing.ResidueField O) W
  freeW : Module.Free (IsLocalRing.ResidueField O) W
  rhoBar : GaloisRep F (IsLocalRing.ResidueField O) W
  residual : IsSemisimplifiedResidualModel rho0 rhoBar
```

This exact data-only form elaborated read-only. A following probe must separately specialize `ResidualModelsAgreeAfterExtension` to the fixed common field `AlgebraicClosure (ZMod p)` with explicit embeddings and topology. No files were edited or promoted by the reviewer.
