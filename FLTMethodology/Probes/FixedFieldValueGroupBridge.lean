/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Fixed-field value-group bridge probe

The first structural prerequisite for identifying the local inertia fixed field with an
unramified extension is normality of the local inertia subgroup.  The chosen integral-closure
valuation ring is local, so its unique maximal ideal is stable under every absolute Galois
automorphism.  Conjugating an automorphism that is trivial modulo that ideal therefore preserves
the inertia condition.
-/

@[expose] public section

open scoped Pointwise
open NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

local notation "Kᵥ" => adicCompletion K v
local notation "𝒪ᵥ" => adicCompletionIntegers K v
local notation "Kᵥᵃˡᵍ" => AlgebraicClosure Kᵥ
local notation "Γᵥ" => Field.absoluteGaloisGroup Kᵥ

attribute [local instance 100000] mulSemiringActionIntegralClosure

/-- The local inertia subgroup used by the FLT development is normal in the absolute Galois
group.  This is the first honest Galois-theoretic bridge toward treating its fixed field as an
unramified extension. -/
instance localInertiaGroup_normal : (localInertiaGroup v).Normal := by
  let B := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
  let I : Ideal B := IsLocalRing.maximalIdeal B
  have hstable (σ : Γᵥ) : σ • I = I := by
    apply IsLocalRing.eq_maximalIdeal
    rw [I.pointwise_smul_eq_comap]
    infer_instance
  rw [localInertiaGroup]
  refine ⟨?_⟩
  intro σ hσ τ
  change ∀ x, (τ * σ * τ⁻¹) • x - x ∈ I
  intro x
  have h := hσ (τ⁻¹ • x)
  have h' : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul τ _ I h
  rw [hstable τ] at h'
  simpa [smul_sub, mul_smul] using h'

#print axioms localInertiaGroup_normal

/-- Normality plus the infinite Galois correspondence identifies the local inertia fixed field as
a Galois extension of the completed base field.  This is structural progress only: unramifiedness
and equality of value groups remain separate obligations. -/
theorem fixedField_localInertia_isGalois :
    IsGalois Kᵥ (IntermediateField.fixedField (localInertiaGroup v)) := by
  rw [← InfiniteGalois.normal_iff_isGalois]
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (⟨localInertiaGroup v, isClosed_localInertiaGroup v⟩ :
      ClosedSubgroup (Field.absoluteGaloisGroup Kᵥ))]
  infer_instance

#print axioms fixedField_localInertia_isGalois

end IsDedekindDomain.HeightOneSpectrum
