import FLT.GaloisRepresentation.Automorphic
import FLT.Deformations.Representable
import FLT.Patching.REqualsT
import FLT.GaloisRepresentation.HardlyRamified.Defs
import Mathlib.RepresentationTheory.Semisimple

/-!
Kernel probe for the current Taylor-2018 modularity-lifting boundary.

This verifies only declarations that actually exist. The missing source vocabulary is represented
as graph definition gaps rather than fabricated placeholder propositions.
-/

namespace FLTMethodology.Taylor2018

open scoped TensorProduct

/-- The integral-model part of the Taylor-2018 coefficient boundary.

This deliberately stops before semisimplification of the residual representation, whose
source-faithful API is absent at the frozen FLT snapshot.
-/
def HasIntegralModel
    {F : Type*} [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[p]) V]
      [Module.Finite (AlgebraicClosure ℚ_[p]) V] [Module.Free (AlgebraicClosure ℚ_[p]) V]
    (ρ : GaloisRep F (AlgebraicClosure ℚ_[p]) V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[p] R) (_ : IsLocalRing R) (_ : IsDomain R)
    (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R) (_ : IsModuleTopology ℤ_[p] R)
    (_ : Algebra R (AlgebraicClosure ℚ_[p]))
    (_ : IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p]))
    (_ : ContinuousSMul R (AlgebraicClosure ℚ_[p]))
    (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
    (_ : Module.Free R V₀) (_ : Module.rank R V₀ = 2)
    (ρ₀ : GaloisRep F R V₀)
    (r₀ : (AlgebraicClosure ℚ_[p]) ⊗[R] V₀ ≃ₗ[AlgebraicClosure ℚ_[p]] V),
      (ρ₀.baseChange (AlgebraicClosure ℚ_[p])).conj r₀ = ρ

/-- A semisimple residual representation whose characteristic polynomials agree with the reduction
of a chosen integral model.

This is a source-level relation, not a construction of semisimplification. It prevents a generic
`Prop` placeholder from hiding the precise residual comparison while leaving the existence and
lattice-independence theorems as explicit missing mathematics.
-/
def IsSemisimplifiedResidualModel
    {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [IsLocalRing R]
      [TopologicalSpace R] [IsTopologicalRing R]
    {V₀ : Type*} [AddCommGroup V₀] [Module R V₀]
      [Module.Finite R V₀] [Module.Free R V₀]
    (ρ₀ : GaloisRep F R V₀)
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
      [Algebra R k] [ContinuousSMul R k]
    {W : Type*} [AddCommGroup W] [Module k W]
      [Module.Finite k W] [Module.Free k W]
    (ρbar : GaloisRep F k W) : Prop :=
  IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R k) ∧
    Representation.IsSemisimpleRepresentation ρbar.toRepresentation ∧
    ∀ σ, ((ρ₀.baseChange k) σ).charpoly = (ρbar σ).charpoly

/-- Isomorphism of two chosen semisimple residual models. -/
def SemisimpleResidualEquivalent
    {F k W₁ W₂ : Type*} [Field F] [NumberField F]
    [Field k] [TopologicalSpace k]
    [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂]
    (ρ₁ : GaloisRep F k W₁) (ρ₂ : GaloisRep F k W₂) : Prop :=
  ∃ e : W₁ ≃ₗ[k] W₂, ρ₁.conj e = ρ₂

/-- Compare residual models after extending their possibly different residue fields to one common
coefficient field. -/
def ResidualModelsAgreeAfterExtension
    {F k₁ k₂ kbar W₁ W₂ : Type*} [Field F] [NumberField F]
    [Field k₁] [TopologicalSpace k₁] [IsTopologicalRing k₁]
    [Field k₂] [TopologicalSpace k₂] [IsTopologicalRing k₂]
    [Field kbar] [TopologicalSpace kbar] [IsTopologicalRing kbar]
    [Algebra k₁ kbar] [ContinuousSMul k₁ kbar]
    [Algebra k₂ kbar] [ContinuousSMul k₂ kbar]
    [AddCommGroup W₁] [Module k₁ W₁] [Module.Finite k₁ W₁] [Module.Free k₁ W₁]
    [AddCommGroup W₂] [Module k₂ W₂] [Module.Finite k₂ W₂] [Module.Free k₂ W₂]
    (ρ₁ : GaloisRep F k₁ W₁) (ρ₂ : GaloisRep F k₂ W₂) : Prop :=
  SemisimpleResidualEquivalent (ρ₁.baseChange kbar) (ρ₂.baseChange kbar)

/-- Exact same-field uniqueness claim left for the Brauer--Nesbitt proof node. This definition
freezes the proposition only; it does not prove it. -/
def SemisimplifiedResidualModelsUnique
    {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [IsLocalRing R]
      [TopologicalSpace R] [IsTopologicalRing R]
    {V₀ : Type*} [AddCommGroup V₀] [Module R V₀]
      [Module.Finite R V₀] [Module.Free R V₀]
    (ρ₀ : GaloisRep F R V₀)
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
      [Algebra R k] [ContinuousSMul R k]
    {W₁ W₂ : Type*}
      [AddCommGroup W₁] [Module k W₁] [Module.Finite k W₁] [Module.Free k W₁]
      [AddCommGroup W₂] [Module k W₂] [Module.Finite k W₂] [Module.Free k W₂]
    (ρbar₁ : GaloisRep F k W₁) (ρbar₂ : GaloisRep F k W₂) : Prop :=
  IsSemisimplifiedResidualModel ρ₀ ρbar₁ →
    IsSemisimplifiedResidualModel ρ₀ ρbar₂ →
    SemisimpleResidualEquivalent ρbar₁ ρbar₂

#check HasIntegralModel
#check IsSemisimplifiedResidualModel
#check SemisimpleResidualEquivalent
#check ResidualModelsAgreeAfterExtension
#check SemisimplifiedResidualModelsUnique
#print axioms HasIntegralModel
#print axioms IsSemisimplifiedResidualModel
#print axioms SemisimpleResidualEquivalent
#print axioms ResidualModelsAgreeAfterExtension
#print axioms SemisimplifiedResidualModelsUnique

end FLTMethodology.Taylor2018

#check GaloisRep
#check GaloisRep.baseChange
#check GaloisRep.IsIrreducible
#check GaloisRep.IsFlatAt
#check GaloisRep.IsAutomorphicOfLevel
#check cyclic_base_change
#check Deformation.narrowSLiftFunctor
#check Deformation.isCorepresentable_narrowSLiftFunctor
#check ker_RtoT_le_nilradical
#check GaloisRepresentation.IsHardlyRamified

#print axioms GaloisRep.IsAutomorphicOfLevel
#print axioms cyclic_base_change
#print axioms Deformation.isCorepresentable_narrowSLiftFunctor
#print axioms ker_RtoT_le_nilradical
