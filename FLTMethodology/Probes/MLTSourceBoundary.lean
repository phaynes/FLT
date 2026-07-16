import FLT.GaloisRepresentation.Automorphic
import FLT.Deformations.Representable
import FLT.Patching.REqualsT
import FLT.GaloisRepresentation.HardlyRamified.Defs

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

#check HasIntegralModel
#print axioms HasIntegralModel

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
