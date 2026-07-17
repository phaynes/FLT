import FLT.AutomorphicForm.QuaternionAlgebra.Basic

open IsQuaternionAlgebra.NumberField
open scoped FLT TensorProduct NumberField Adele

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct

open ConjAct Pointwise

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]
variable (R : Type*) [CommRing R]

/--
Signature-only probe for the Fable advisory quaternion T2 boundary. The proposed theorem is a local
hypothesis, not a repository axiom. This checks that its spelling elaborates and definitionally
supplies the exact existing `LevelStruct.isFiniteRelIndex_Δ` consumer.
-/
theorem quaternion_stabilizer_signature_applies [NumberField.IsTotallyReal F]
    [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (ℒ : WeightTwoAutomorphicForm.LevelStruct F R) (g : GL₂(𝔸ᶠ[F]))
    (historicalStabilizerFiniteness :
      Subgroup.IsFiniteRelIndex
        (MonoidHom.range
          (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F])))))
        ((ℒ.U ⊔ MonoidHom.range
            (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]))))) ⊓
          toConjAct g⁻¹ • MonoidHom.range (WithRigidification.unitsIncl F D))) :
    Subgroup.IsFiniteRelIndex
      (MonoidHom.range
        (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F])))))
      (ℒ.Δ D g) := by
  exact historicalStabilizerFiniteness

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct

#print axioms
  TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.quaternion_stabilizer_signature_applies
