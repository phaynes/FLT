import FLTMethodology.Probes.BrauerNesbittBoundary
import FLT.Components.BrauerNesbitt.RankTwo
import FLT.GaloisRepresentation.HardlyRamified.Lift
import FLT.GaloisRepresentation.HardlyRamified.Family
import FLT.Deformations.Categories
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
Kernel-clean bounded coefficient/lattice/residual vocabulary for the FLT modularity-lifting
programme. The existence providers remain explicit open obligations in the control graph.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FLTMethodology.Taylor2018.Coefficients

open scoped TensorProduct
open FLTMethodology.Taylor2018 FLTProbe.BrauerNesbitt IsLocalRing

universe uO uF uE uV uV01 uV02 uW1 uW2 uC uV0 uW0

/-! ### U1 : stable-lattice bundle -/

structure StableLatticeData
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (O : Type uO) {F : Type uF} {E : Type uE} {V : Type uV}
    [Field F] [NumberField F]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
    [Field E] [Algebra O E] [IsFractionRing O E]
    [TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
    [IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
    [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
    (hV : Module.rank E V = 2) (rho : GaloisRep F E V) where
  V0 : Type uV01
  [addCommGroupV0 : AddCommGroup V0]
  [moduleV0 : Module O V0]
  [finiteV0 : Module.Finite O V0]
  [freeV0 : Module.Free O V0]
  rankV0 : Module.rank O V0 = 2
  rho0 : GaloisRep F O V0
  r0 : E ⊗[O] V0 ≃ₗ[E] V
  compat : (rho0.baseChange E).conj r0 = rho

attribute [instance] StableLatticeData.addCommGroupV0 StableLatticeData.moduleV0
  StableLatticeData.finiteV0 StableLatticeData.freeV0

/-! ### U2 : coefficient bundle, `extends` form (Stage-5 item 3) -/

set_option linter.checkUnivs false in
structure CoefficientData
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (O : Type uO) {F : Type uF} {E : Type uE} {V : Type uV}
    [Field F] [NumberField F]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
    [IsNoetherianRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O]
    [Field E] [Algebra O E] [IsFractionRing O E]
    [TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
    [IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
    [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
    [DiscreteTopology (ResidueField O)] [ContinuousSMul O (ResidueField O)]
    [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
    (hV : Module.rank E V = 2) (rho : GaloisRep F E V)
    extends StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho where
  Wbar : Type uW1
  [addCommGroupWbar : AddCommGroup Wbar]
  [moduleWbar : Module (ResidueField O) Wbar]
  [finiteWbar : Module.Finite (ResidueField O) Wbar]
  [freeWbar : Module.Free (ResidueField O) Wbar]
  rhobar : GaloisRep F (ResidueField O) Wbar
  isSemisimplifiedResidualModel : IsSemisimplifiedResidualModel rho0 rhobar

attribute [instance] CoefficientData.addCommGroupWbar CoefficientData.moduleWbar
  CoefficientData.finiteWbar CoefficientData.freeWbar


/-! ### Generic-closure tower (Stage-5 item 1): explicit replacement wrapper -/

structure GenericClosureTower
    (p : ℕ) [Fact p.Prime]
    (O : Type uO) (E : Type uE)
    [CommRing O] [TopologicalSpace O] [Field E] [TopologicalSpace E] [Algebra O E] where
  [algebraO : Algebra O (AlgebraicClosure ℚ_[p])]
  [algebraE : Algebra E (AlgebraicClosure ℚ_[p])]
  [tower : IsScalarTower O E (AlgebraicClosure ℚ_[p])]
  [contO : ContinuousSMul O (AlgebraicClosure ℚ_[p])]
  [contE : ContinuousSMul E (AlgebraicClosure ℚ_[p])]

/-! ### U3 : residual-closure comparison with explicit embeddings -/

/-- The fixed residual closure carries its canonical discrete topology (probe-local instances;
scoped in production). -/
noncomputable local instance residualClosureTopology (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (AlgebraicClosure (ZMod p)) := ⊥

local instance residualClosureDiscrete (p : ℕ) [Fact p.Prime] :
    DiscreteTopology (AlgebraicClosure (ZMod p)) := ⟨rfl⟩

def AgreeInResidualClosure
    (p : ℕ) [Fact p.Prime]
    {F : Type uF} [Field F] [NumberField F]
    {k1 : Type uO} [Field k1] [TopologicalSpace k1] [IsTopologicalRing k1] [DiscreteTopology k1]
    {k2 : Type uO} [Field k2] [TopologicalSpace k2] [IsTopologicalRing k2] [DiscreteTopology k2]
    {W1 : Type uW1} [AddCommGroup W1] [Module k1 W1] [Module.Finite k1 W1] [Module.Free k1 W1]
    {W2 : Type uW2} [AddCommGroup W2] [Module k2 W2] [Module.Finite k2 W2] [Module.Free k2 W2]
    (rhobar1 : GaloisRep F k1 W1) (rhobar2 : GaloisRep F k2 W2)
    (f1 : k1 →+* AlgebraicClosure (ZMod p)) (f2 : k2 →+* AlgebraicClosure (ZMod p)) : Prop :=
  letI := f1.toAlgebra
  letI := f2.toAlgebra
  haveI : ContinuousSMul k1 (AlgebraicClosure (ZMod p)) := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousSMul k2 (AlgebraicClosure (ZMod p)) := ⟨continuous_of_discreteTopology⟩
  ResidualModelsAgreeAfterExtension (kbar := AlgebraicClosure (ZMod p)) rhobar1 rhobar2

/-! ### M4 : semisimplicity-ascent contract (open; consumed only as hypothesis) -/

def SemisimpleAscendsToResidualClosureContract : Prop :=
  ∀ {F : Type uF} [Field F] [NumberField F]
    {k : Type uO} [Field k] [Finite k] [TopologicalSpace k] [IsTopologicalRing k]
      [DiscreteTopology k]
    {kbar : Type uO} [Field kbar] [IsAlgClosed kbar] [TopologicalSpace kbar]
      [IsTopologicalRing kbar]
    [Algebra k kbar] [ContinuousSMul k kbar]
    {W : Type uW1} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (rhobar : GaloisRep F k W),
    Representation.IsSemisimpleRepresentation rhobar.toRepresentation →
    Representation.IsSemisimpleRepresentation (rhobar.baseChange kbar).toRepresentation

/-! ### Pointwise base-change lemma -/

theorem galoisRep_baseChange_apply
    {F : Type uF} [Field F]
    {A : Type uO} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type uE} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra A B] [ContinuousSMul A B]
    {M : Type uV01} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (rho : GaloisRep F A M) (σ : Field.absoluteGaloisGroup F) :
    rho.baseChange B σ = LinearMap.baseChange B (rho σ) := rfl

/-! ### Stage-3 shared context for the remaining units -/

section Units

variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (O : Type uO) {F : Type uF} {E : Type uE} {V : Type uV}
    [Field F] [NumberField F]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
    [IsNoetherianRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O]
    [Field E] [Algebra O E] [IsFractionRing O E]
    [TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
    [IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
    [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
    [DiscreteTopology (ResidueField O)] [ContinuousSMul O (ResidueField O)]
    [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
    (hV : Module.rank E V = 2) (rho : GaloisRep F E V)

/-- A1' -/
def HasStableLattice : Prop :=
  Nonempty (StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho)

/-- A3' -/
def HasSemisimplifiedReduction
    (D : StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho) : Prop :=
  ∃ (Wbar : Type uW1) (_ : AddCommGroup Wbar) (_ : Module (ResidueField O) Wbar)
    (_ : Module.Finite (ResidueField O) Wbar) (_ : Module.Free (ResidueField O) Wbar)
    (rhobar : GaloisRep F (ResidueField O) Wbar),
    IsSemisimplifiedResidualModel D.rho0 rhobar

/-- Consumer-shaped closure descent (exact `cyclic_base_change`/`mem_isCompatible` boundary). -/
def DescendsToClosure
    (D : StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho)
    (T : GenericClosureTower p O E)
    {Vc : Type uV} [AddCommGroup Vc] [Module (AlgebraicClosure ℚ_[p]) Vc]
    [Module.Finite (AlgebraicClosure ℚ_[p]) Vc] [Module.Free (AlgebraicClosure ℚ_[p]) Vc]
    (rhoc : GaloisRep F (AlgebraicClosure ℚ_[p]) Vc) : Prop :=
  letI := T.algebraO
  letI := T.contO
  ∃ rc : (AlgebraicClosure ℚ_[p]) ⊗[O] D.V0 ≃ₗ[AlgebraicClosure ℚ_[p]] Vc,
    (D.rho0.baseChange (AlgebraicClosure ℚ_[p])).conj rc = rhoc

/-- The integral model base-changed to the generic closure, consumer-exact instance form. -/
noncomputable def closureModel
    [Algebra O (AlgebraicClosure ℚ_[p])] [ContinuousSMul O (AlgebraicClosure ℚ_[p])]
    (D : StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho) :
    GaloisRep F (AlgebraicClosure ℚ_[p]) ((AlgebraicClosure ℚ_[p]) ⊗[O] D.V0) :=
  D.rho0.baseChange (AlgebraicClosure ℚ_[p])

/-- L1a -/
theorem charpoly_baseChange_eq_of_generic
    (D1 : StableLatticeData.{uO, uF, uE, uV, uV01} p hp O hV rho)
    (D2 : StableLatticeData.{uO, uF, uE, uV, uV02} p hp O hV rho)
    (σ : Field.absoluteGaloisGroup F) :
    (D1.rho0 σ).charpoly = (D2.rho0 σ).charpoly := by
  have hpt1 := DFunLike.congr_fun D1.compat σ
  have hpt2 := DFunLike.congr_fun D2.compat σ
  have h1 : (rho σ).charpoly = (D1.rho0 σ).charpoly.map (algebraMap O E) := by
    rw [← hpt1, GaloisRep.conj_apply, LinearEquiv.charpoly_conj,
      galoisRep_baseChange_apply, LinearMap.charpoly_baseChange]
  have h2 : (rho σ).charpoly = (D2.rho0 σ).charpoly.map (algebraMap O E) := by
    rw [← hpt2, GaloisRep.conj_apply, LinearEquiv.charpoly_conj,
      galoisRep_baseChange_apply, LinearMap.charpoly_baseChange]
  exact Polynomial.map_injective (algebraMap O E) (IsFractionRing.injective O E)
    (h1.symm.trans h2)

/-- L1b -/
theorem residual_charpoly_eq_of_two_integral_models
    (D1 : CoefficientData.{uO, uF, uE, uV, uV01, uW1} p hp O hV rho)
    (D2 : CoefficientData.{uO, uF, uE, uV, uV02, uW2} p hp O hV rho)
    (σ : Field.absoluteGaloisGroup F) :
    (D1.rhobar σ).charpoly = (D2.rhobar σ).charpoly := by
  have h0 := charpoly_baseChange_eq_of_generic p hp O hV rho
    D1.toStableLatticeData D2.toStableLatticeData σ
  have h1 := D1.isSemisimplifiedResidualModel.2.2 σ
  have h2 := D2.isSemisimplifiedResidualModel.2.2 σ
  rw [← h1, ← h2, galoisRep_baseChange_apply, galoisRep_baseChange_apply,
    LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, h0]

/-- Residual rank transport at bundle level. -/
theorem CoefficientData.finrank_wbar_eq_two
    (D : CoefficientData.{uO, uF, uE, uV, uV01, uW1} p hp O hV rho) :
    Module.finrank (ResidueField O) D.Wbar = 2 :=
  residualModel_finrank_eq_two D.rho0 D.rhobar D.rankV0 D.isSemisimplifiedResidualModel

/-- U4 -/
def LatticeIndependent : Prop :=
  ∀ (D1 : CoefficientData.{uO, uF, uE, uV, uV01, uW1} p hp O hV rho)
    (D2 : CoefficientData.{uO, uF, uE, uV, uV02, uW2} p hp O hV rho),
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar

/-- A4', pointwise form, with fully generalized module universes. -/
theorem latticeIndependent_of_groupContract
    (hBN : GroupContract.{uO, uF, uW1, uW2})
    (D1 : CoefficientData.{uO, uF, uE, uV, uV01, uW1} p hp O hV rho)
    (D2 : CoefficientData.{uO, uF, uE, uV, uV02, uW2} p hp O hV rho) :
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar := by
  have hs1 : Representation.IsSemisimpleRepresentation D1.rhobar.toRepresentation :=
    D1.isSemisimplifiedResidualModel.2.1
  have hs2 : Representation.IsSemisimpleRepresentation D2.rhobar.toRepresentation :=
    D2.isSemisimplifiedResidualModel.2.1
  have hchar : ∀ g, (D1.rhobar.toRepresentation g).charpoly
      = (D2.rhobar.toRepresentation g).charpoly :=
    fun g => residual_charpoly_eq_of_two_integral_models p hp O hV rho D1 D2 g
  obtain ⟨e⟩ := hBN D1.rhobar.toRepresentation D2.rhobar.toRepresentation hs1 hs2 hchar
  refine ⟨e.toLinearEquiv, ?_⟩
  apply GaloisRep.ext
  intro g
  exact e.conj_apply_self g

/-- A4', bundle form. -/
theorem latticeIndependent_of_groupContract'
    (hBN : GroupContract.{uO, uF, uW1, uW2}) :
    LatticeIndependent.{uO, uF, uE, uV, uV01, uV02, uW1, uW2} p hp O hV rho :=
  fun D1 D2 => latticeIndependent_of_groupContract p hp O hV rho hBN D1 D2

/-- The rank-two Brauer--Nesbitt theorem discharges the comparison provider for the bounded
coefficient-data consumer. Unlike `latticeIndependent_of_groupContract`, this theorem does not
receive a Brauer--Nesbitt proposition as an assumption: the rank facts stored in each coefficient
bundle and the already-proved characteristic-polynomial comparison supply all of its premises. -/
theorem latticeIndependent_rankTwo
    (D1 : CoefficientData.{uO, uF, uE, uV, uV01, uW1} p hp O hV rho)
    (D2 : CoefficientData.{uO, uF, uE, uV, uV02, uW2} p hp O hV rho) :
    SemisimpleResidualEquivalent D1.rhobar D2.rhobar := by
  have hs1 : Representation.IsSemisimpleRepresentation D1.rhobar.toRepresentation :=
    D1.isSemisimplifiedResidualModel.2.1
  have hs2 : Representation.IsSemisimpleRepresentation D2.rhobar.toRepresentation :=
    D2.isSemisimplifiedResidualModel.2.1
  have hchar : ∀ g, (D1.rhobar.toRepresentation g).charpoly
      = (D2.rhobar.toRepresentation g).charpoly :=
    fun g => residual_charpoly_eq_of_two_integral_models p hp O hV rho D1 D2 g
  obtain ⟨e⟩ :=
    FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two
      D1.rhobar.toRepresentation D2.rhobar.toRepresentation hs1 hs2
      (D1.finrank_wbar_eq_two p hp O hV rho)
      (D2.finrank_wbar_eq_two p hp O hV rho) hchar
  refine ⟨e.toLinearEquiv, ?_⟩
  apply GaloisRep.ext
  intro g
  exact e.conj_apply_self g

/-- Bundle form of the now-unconditional rank-two lattice-independence consumer. -/
theorem latticeIndependent_rankTwo' :
    LatticeIndependent.{uO, uF, uE, uV, uV01, uV02, uW1, uW2} p hp O hV rho :=
  fun D1 D2 => latticeIndependent_rankTwo p hp O hV rho D1 D2

#print axioms latticeIndependent_rankTwo
#print axioms latticeIndependent_rankTwo'

/-- T-A2a residue local-hom adapter (open named boundary; NOT proved). -/
def ResidueLocalHomAdapter
    [Algebra ℤ_[p] (ResidueField O)] [IsScalarTower ℤ_[p] O (ResidueField O)] : Prop :=
  IsLocalHom (algebraMap ℤ_[p] (ResidueField O))

/-- T-A2 coefficient glue (open named boundary; NOT proved). -/
def CoefficientGlueContract
    [Algebra ℤ_[p] (ResidueField O)] [IsScalarTower ℤ_[p] O (ResidueField O)] : Prop :=
  IsNoetherianRing O ∧ Finite (ResidueField O) ∧
    IsAdicComplete (maximalIdeal O) O ∧
    IsLocalHom (algebraMap ℤ_[p] (ResidueField O))

end Units


open scoped TensorProduct

variable {F : Type uF} [Field F] [NumberField F]
    {O : Type uO} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {E : Type uE} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    [Algebra O E] [ContinuousSMul O E]
    {C : Type uC} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [Algebra O C] [Algebra E C] [IsScalarTower O E C]
    [ContinuousSMul O C] [ContinuousSMul E C]
    {V0 : Type uV0} [AddCommGroup V0] [Module O V0] [Module.Finite O V0] [Module.Free O V0]
    {V : Type uV} [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]

/-- Base change through a tower agrees with one-step base change, up to `cancelBaseChange`. -/
theorem galoisRep_baseChange_baseChange (rho0 : GaloisRep F O V0) :
    (rho0.baseChange E).baseChange C =
      (rho0.baseChange C).conj
        (TensorProduct.AlgebraTensorModule.cancelBaseChange O E C C V0).symm := by
  apply GaloisRep.ext
  intro σ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul e v =>
          simp [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      | add a b ha hb =>
          simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Base change commutes with conjugation. -/
theorem galoisRep_baseChange_conj
    {W0 : Type uW0} [AddCommGroup W0] [Module E W0] [Module.Finite E W0] [Module.Free E W0]
    (rho' : GaloisRep F E W0) (e : W0 ≃ₗ[E] V) :
    (rho'.conj e).baseChange C = (rho'.baseChange C).conj (e.baseChange (A := C)) := by
  apply GaloisRep.ext
  intro σ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Consumer-shaped closure descent: an integral model of `rho` descends any base change of
`rho`, in exactly the `cyclic_base_change`/`mem_isCompatible` existential shape. -/
theorem exists_closure_descent
    {V0mod : Type uV0} [AddCommGroup V0mod] [Module O V0mod]
    [Module.Finite O V0mod] [Module.Free O V0mod]
    (rho0 : GaloisRep F O V0mod) (rho : GaloisRep F E V)
    (r0 : E ⊗[O] V0mod ≃ₗ[E] V)
    (hcompat : (rho0.baseChange E).conj r0 = rho) :
    ∃ rc : C ⊗[O] V0mod ≃ₗ[C] C ⊗[E] V,
      (rho0.baseChange C).conj rc = rho.baseChange C := by
  have h1 := galoisRep_baseChange_conj (C := C) (rho0.baseChange E) r0
  have h2 := galoisRep_baseChange_baseChange (C := C) (E := E) rho0
  refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange O E C C V0mod).symm.trans
    (r0.baseChange (A := C)), ?_⟩
  have hrho : rho.baseChange C = ((rho0.baseChange E).conj r0).baseChange C := by rw [hcompat]
  rw [hrho, h1, h2]
  apply GaloisRep.ext
  intro σ
  apply LinearMap.ext
  intro x
  simp

/-- The open field-of-definition provider that identifies a named closure-valued consumer with the
finite coefficient-field representation after base change. -/
def NamedClosureRealization
    {Vc : Type uW0} [AddCommGroup Vc] [Module C Vc]
    (rho : GaloisRep F E V) (rhoc : GaloisRep F C Vc) : Prop :=
  ∃ ec : C ⊗[E] V ≃ₗ[C] Vc, (rho.baseChange C).conj ec = rhoc

/-- Conditional closure descent to the named representation used by a live consumer.

The realization is deliberately a hypothesis: constructing it is the open
`FLT-MLT-COEFF-REALIZATION` provider, not an axiom hidden in this theorem. -/
theorem exists_descent_to_named_consumer
    {Vc : Type uW0} [AddCommGroup Vc] [Module C Vc]
    {V0mod : Type uV0} [AddCommGroup V0mod] [Module O V0mod]
    [Module.Finite O V0mod] [Module.Free O V0mod]
    (rho0 : GaloisRep F O V0mod) (rho : GaloisRep F E V)
    (r0 : E ⊗[O] V0mod ≃ₗ[E] V)
    (hcompat : (rho0.baseChange E).conj r0 = rho)
    (rhoc : GaloisRep F C Vc)
    (hrealization : NamedClosureRealization rho rhoc) :
    ∃ rc : C ⊗[O] V0mod ≃ₗ[C] Vc,
      (rho0.baseChange C).conj rc = rhoc := by
  obtain ⟨ec, hconsumer⟩ := hrealization
  obtain ⟨rc, hrc⟩ := exists_closure_descent (C := C) rho0 rho r0 hcompat
  refine ⟨rc.trans ec, ?_⟩
  calc
    (rho0.baseChange C).conj (rc.trans ec) =
        ((rho0.baseChange C).conj rc).conj ec := by
      apply GaloisRep.ext
      intro σ
      exact congrArg (fun f => f ((rho0.baseChange C) σ))
        (LinearEquiv.conj_trans rc ec).symm
    _ = (rho.baseChange C).conj ec := by rw [hrc]
    _ = rhoc := hconsumer


end FLTMethodology.Taylor2018.Coefficients
