import Mathlib.FieldTheory.LinearDisjoint

/-!
# Moret--Bailly field adapter probe

This methodology-only file records the small algebraic consequence used by the proposed
Moret--Bailly specialization: linear disjointness from a compositum implies linear disjointness
from each constituent field. It does not state or assume the Moret--Bailly existence theorem.
-/

namespace FLT.PotentialModularity

universe u v

/-- Disjointness from a compositum supplies disjointness from each field separately. -/
theorem linearDisjoint_of_compositum
    {K : Type u} [Field K] {Omega : Type v} [Field Omega] [Algebra K Omega]
    (L K₁ K₂ : IntermediateField K Omega)
    (h : L.LinearDisjoint
      ((K₁ ⊔ K₂ : IntermediateField K Omega) : Type v)) :
    L.LinearDisjoint K₁ ∧ L.LinearDisjoint K₂ :=
  ⟨h.of_le_right le_sup_left, h.of_le_right le_sup_right⟩

#check linearDisjoint_of_compositum
#print axioms linearDisjoint_of_compositum

end FLT.PotentialModularity
