/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

import FLT.DedekindDomain.AdicValuation
import FLT.NumberField.Completion.Finite
import Mathlib.RingTheory.Invariant.Profinite

/-!
# The uniformizer decomposition in the local inertia fixed field

This file supplies the finite-level ramification theory needed to prove that every nonzero element
of the local inertia fixed field is a power of the chosen base uniformizer times an integral unit.
-/

@[expose] public section

open NumberField
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

/-- The local inertia subgroup is normal in the absolute local Galois group. -/
instance localInertiaGroup_normal : (localInertiaGroup v).Normal := by
  let B := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
  let I : Ideal B := 𝔪 B
  have hstable (σ : Γ Kᵥ) : σ • I = I := by
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

/-- The fixed field of local inertia is Galois over the completed local field. -/
theorem fixedField_localInertia_isGalois :
    IsGalois Kᵥ (IntermediateField.fixedField (localInertiaGroup v)) := by
  rw [← InfiniteGalois.normal_iff_isGalois]
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (⟨localInertiaGroup v, isClosed_localInertiaGroup v⟩ :
      ClosedSubgroup (Γ Kᵥ))]
  infer_instance

/-- The chosen tame uniformizer as an element of the completed valuation ring. -/
noncomputable def tameUniformizerInteger : 𝒪ᵥ :=
  ⟨tameUniformizer v, by
    change Valued.v (tameUniformizer v) ≤ 1
    rw [tameUniformizer_valuation]
    exact WithZero.coe_le_coe.mpr ((Multiplicative.ofAdd_le).mpr (by omega))⟩

@[simp]
theorem tameUniformizerInteger_val : (tameUniformizerInteger v).1 = tameUniformizer v := rfl

/-- The chosen tame uniformizer generates the maximal ideal of the completed valuation ring. -/
theorem maximalIdeal_eq_span_tameUniformizerInteger :
    𝔪 𝒪ᵥ = Ideal.span {tameUniformizerInteger v} :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
    K v (tameUniformizer_valuation v)

/-- The integral closure in a finite intermediate field is a DVR. -/
noncomputable instance finiteIntegralClosure_isDiscreteValuationRing
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    IsDiscreteValuationRing (IntegralClosure 𝒪ᵥ L) := by
  have hdedekind : IsDedekindDomain (IntegralClosure 𝒪ᵥ L) := by
    change IsDedekindDomain (integralClosure 𝒪ᵥ L)
    exact integralClosure.isDedekindDomain 𝒪ᵥ Kᵥ L
  letI := hdedekind
  have h𝒪ᵥ : 𝒪ᵥ ≠ ⊤ := by
    refine fun h ↦ IsDiscreteValuationRing.not_isField 𝒪ᵥ (h ▸ ?_)
    exact (Subring.topEquiv (R := Kᵥ)).isField (Semifield.toIsField Kᵥ)
  exact ((IsDiscreteValuationRing.TFAE (IntegralClosure 𝒪ᵥ L)
    (not_isField_integralClosure (L := L) 𝒪ᵥ h𝒪ᵥ)).out 2 0).mp hdedekind

/-- The integral closure in a finite intermediate field is finite over the base DVR. -/
noncomputable instance finiteIntegralClosure_moduleFinite
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    Module.Finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) := by
  change Module.Finite 𝒪ᵥ (integralClosure 𝒪ᵥ L)
  exact IsIntegralClosure.finite 𝒪ᵥ Kᵥ L (integralClosure 𝒪ᵥ L)

/-- The finite integral closure is free over the base DVR. -/
noncomputable instance finiteIntegralClosure_moduleFree
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    Module.Free 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) := by
  change Module.Free 𝒪ᵥ (integralClosure 𝒪ᵥ L)
  exact IsIntegralClosure.module_free 𝒪ᵥ Kᵥ L (integralClosure 𝒪ᵥ L)

/-- A finite intermediate field is the fraction field of its integral closure. -/
noncomputable instance finiteIntegralClosure_isFractionRing
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    IsFractionRing (IntegralClosure 𝒪ᵥ L) L := by
  change IsFractionRing (integralClosure 𝒪ᵥ L) L
  exact IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ L (integralClosure 𝒪ᵥ L)

/-- Inclusion of finite-level integral closures into the integral closure in the algebraic
closure. -/
noncomputable def finiteIntegralClosureAlgHom
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    IntegralClosure 𝒪ᵥ L →ₐ[𝒪ᵥ] IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ) := by
  change integralClosure 𝒪ᵥ L →ₐ[𝒪ᵥ] integralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
  exact (L.val.restrictScalars 𝒪ᵥ).mapIntegralClosure

noncomputable instance finiteIntegralClosure_algebra
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    Algebra (IntegralClosure 𝒪ᵥ L) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :=
  (finiteIntegralClosureAlgHom v L).toAlgebra

noncomputable instance finiteIntegralClosure_isScalarTower
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    IsScalarTower 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance finiteIntegralClosure_top_isIntegral
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    Algebra.IsIntegral (IntegralClosure 𝒪ᵥ L) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :=
  Algebra.IsIntegral.tower_top 𝒪ᵥ

noncomputable instance finiteIntegralClosure_smulDistribClass
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    SMulDistribClass (L ≃ₐ[Kᵥ] L) (IntegralClosure 𝒪ᵥ L) L where
  smul_distrib_smul σ x y := by
    change σ (x.1 * y) = (σ x.1) * σ y
    exact map_mul σ x.1 y

/-- The infinite maximal ideal contracts to the unique maximal ideal at every finite level. -/
theorem maximalIdeal_integralClosure_comap
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).comap
      (finiteIntegralClosureAlgHom v L) = 𝔪 (IntegralClosure 𝒪ᵥ L) := by
  apply IsLocalRing.eq_maximalIdeal
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

/-- The finite-level maximal ideal lies over the maximal ideal of the base DVR. -/
noncomputable instance finiteIntegralClosure_maximalIdeal_liesOver
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    (𝔪 (IntegralClosure 𝒪ᵥ L)).LiesOver (𝔪 𝒪ᵥ) := inferInstance

/-- Finite extensions of the completed local field have finite residue field. -/
noncomputable instance finiteIntegralClosure_residueField_finite
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    Finite (κ (IntegralClosure 𝒪ᵥ L)) :=
  IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪ᵥ) (S := IntegralClosure 𝒪ᵥ L) inferInstance

/-- The finite Galois group acts as the Galois group of the corresponding integral closures. -/
noncomputable instance finiteIntegralClosure_isGaloisGroup
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L] :
    IsGaloisGroup (L ≃ₐ[Kᵥ] L) 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) :=
  by
    letI : SMulDistribClass (L ≃ₐ[Kᵥ] L) (IntegralClosure 𝒪ᵥ L) L :=
      finiteIntegralClosure_smulDistribClass v L
    exact IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[Kᵥ] L) 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) Kᵥ L

/-- Restricting an infinite inertia element to a finite Galois level gives a finite inertia
element. -/
theorem map_localInertiaGroup_le_finiteInertia
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L] :
    (localInertiaGroup v).map (AlgEquiv.restrictNormalHom L) ≤
      (𝔪 (IntegralClosure 𝒪ᵥ L)).inertia (L ≃ₐ[Kᵥ] L) := by
  rintro _ ⟨σ, hσ, rfl⟩ x
  rw [← maximalIdeal_integralClosure_comap v L]
  have hx := hσ (finiteIntegralClosureAlgHom v L x)
  change finiteIntegralClosureAlgHom v L
      ((AlgEquiv.restrictNormalHom L) σ • x - x) ∈
    𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))
  rw [map_sub]
  have hsmul : finiteIntegralClosureAlgHom v L
      ((AlgEquiv.restrictNormalHom L) σ • x) =
      σ • finiteIntegralClosureAlgHom v L x := by
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom L) σ x.1).1 = σ x.1.1
    rw [AlgEquiv.restrictNormalHom_apply]
  rw [hsmul]
  exact hx

/-- The subgroup fixing a finite field commutes with scalar multiplication by its finite integral
closure on the infinite integral closure. -/
noncomputable instance fixingSubgroup_smulCommClass_integralClosure
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    SMulCommClass L.fixingSubgroup (IntegralClosure 𝒪ᵥ L)
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) where
  smul_comm σ x y := by
    apply Subtype.ext
    change σ.1 (x.1.1 * y.1) = x.1.1 * σ.1 y.1
    rw [map_mul, show σ.1 x.1.1 = x.1.1 from σ.2 x.1]

/-- Discrete continuity of the integral-closure action restricts to every finite fixing
subgroup. -/
noncomputable instance fixingSubgroup_continuousSMulDiscrete_integralClosure
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    ContinuousSMulDiscrete L.fixingSubgroup (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) where
  isOpen_smul_eq x y :=
    (ContinuousSMulDiscrete.isOpen_smul_eq (Γ Kᵥ) x y).preimage continuous_subtype_val

/-- The elements of the infinite integral closure fixed by the subgroup fixing `L` are exactly
the images of the integral closure in `L`. -/
theorem isInvariant_finiteIntegralClosure_fixingSubgroup
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    Algebra.IsInvariant (IntegralClosure 𝒪ᵥ L)
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) L.fixingSubgroup := by
  constructor
  intro x hx
  have hxL : x.1 ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    intro σ
    exact congrArg Subtype.val (hx σ)
  let xL : L := ⟨x.1, hxL⟩
  have hxint : IsIntegral 𝒪ᵥ xL :=
    (isIntegral_algHom_iff (L.val.restrictScalars 𝒪ᵥ) L.val.injective).mp x.2
  refine ⟨⟨xL, hxint⟩, ?_⟩
  apply Subtype.ext
  rfl

noncomputable instance finiteIntegralClosure_fixingSubgroup_isInvariant
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) :
    Algebra.IsInvariant (IntegralClosure 𝒪ᵥ L)
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) L.fixingSubgroup :=
  isInvariant_finiteIntegralClosure_fixingSubgroup v L

/-- The infinite maximal ideal lies over the finite-level maximal ideal. -/
noncomputable instance infiniteMaximalIdeal_liesOver_finiteMaximalIdeal
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] :
    (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).LiesOver
      (𝔪 (IntegralClosure 𝒪ᵥ L)) where
  over := (maximalIdeal_integralClosure_comap v L).symm

/-- Every finite inertia automorphism lifts to an element of the absolute local inertia group.

An arbitrary absolute Galois lift need not lie in inertia. Its residue action is corrected by an
element of the subgroup fixing `L`, supplied by profinite surjectivity of the residue stabilizer
map. The product is `σ * ρ⁻¹`: it has the same restriction as `σ` and trivial residue action. -/
theorem finiteInertia_le_map_localInertiaGroup
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L] :
    (𝔪 (IntegralClosure 𝒪ᵥ L)).inertia (L ≃ₐ[Kᵥ] L) ≤
      (localInertiaGroup v).map (AlgEquiv.restrictNormalHom L) := by
  classical
  intro τ hτ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (Kᵥᵃˡᵍ) τ
  let B := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
  let A := IntegralClosure 𝒪ᵥ L
  let Q : Ideal B := 𝔪 B
  let P : Ideal A := 𝔪 A
  letI : Q.LiesOver P := infiniteMaximalIdeal_liesOver_finiteMaximalIdeal v L
  letI : Algebra (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebraOfLiesOver Q P
  have hQstable (g : Γ Kᵥ) : g • Q = Q := by
    apply IsLocalRing.eq_maximalIdeal
    rw [Q.pointwise_smul_eq_comap]
    infer_instance
  let residueAction : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q :=
    { __ := Ideal.quotientEquiv Q Q
        (MulSemiringAction.toRingEquiv (Γ Kᵥ) B σ) (hQstable σ).symm
      commutes' := by
        rintro ⟨x⟩
        have hx := hτ x
        rw [← maximalIdeal_integralClosure_comap v L] at hx
        change finiteIntegralClosureAlgHom v L
            ((AlgEquiv.restrictNormalHom L) σ • x - x) ∈ Q at hx
        rw [map_sub] at hx
        have hsmul : finiteIntegralClosureAlgHom v L
            ((AlgEquiv.restrictNormalHom L) σ • x) =
            σ • finiteIntegralClosureAlgHom v L x := by
          apply Subtype.ext
          change ((AlgEquiv.restrictNormalHom L) σ x.1).1 = σ x.1.1
          rw [AlgEquiv.restrictNormalHom_apply]
        rw [hsmul] at hx
        exact Ideal.Quotient.eq.2 hx }
  letI : CompactSpace L.fixingSubgroup :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : ContinuousSMul L.fixingSubgroup B := inferInstance
  obtain ⟨ρ, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := L.fixingSubgroup) P Q residueAction
  let ρΓ : Γ Kᵥ := ρ.1.1
  have hresidue (y : B) :
      Ideal.Quotient.mk Q (ρΓ • y) = Ideal.Quotient.mk Q (σ • y) := by
    have h := DFunLike.congr_fun hρ (Ideal.Quotient.mk Q y)
    exact h
  have hcorrected : σ * ρΓ⁻¹ ∈ localInertiaGroup v := by
    intro y
    change σ • (ρΓ⁻¹ • y) - y ∈ Q
    rw [← Ideal.Quotient.eq]
    have h := hresidue (ρΓ⁻¹ • y)
    simpa only [smul_inv_smul] using h.symm
  refine ⟨σ * ρΓ⁻¹, hcorrected, ?_⟩
  rw [map_mul, map_inv]
  have hρrestrict : (AlgEquiv.restrictNormalHom L) ρΓ = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact ρ.1.2 x
  rw [hρrestrict, inv_one, mul_one]

/-- Restriction maps infinite local inertia onto finite inertia at every finite Galois level. -/
theorem map_localInertiaGroup_eq_finiteInertia
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L] :
    (localInertiaGroup v).map (AlgEquiv.restrictNormalHom L) =
      (𝔪 (IntegralClosure 𝒪ᵥ L)).inertia (L ≃ₐ[Kᵥ] L) :=
  le_antisymm (map_localInertiaGroup_le_finiteInertia v L)
    (finiteInertia_le_map_localInertiaGroup v L)

/-- A finite Galois subfield of the local inertia fixed field has trivial finite inertia. -/
theorem finiteInertia_eq_bot_of_le_fixedField
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (hL : L ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    (𝔪 (IntegralClosure 𝒪ᵥ L)).inertia (L ≃ₐ[Kᵥ] L) = ⊥ := by
  rw [← map_localInertiaGroup_eq_finiteInertia v L]
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [Subgroup.mem_bot]
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hL x.2 ⟨σ, hσ⟩
  · exact bot_le

/-- A finite Galois subfield of the local inertia fixed field has ramification index one. -/
theorem ramificationIdx_eq_one_of_le_fixedField
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (hL : L ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    (𝔪 (IntegralClosure 𝒪ᵥ L)).ramificationIdx 𝒪ᵥ = 1 := by
  letI : Finite ((𝔪 𝒪ᵥ).ResidueField) := by
    apply (IsLocalization.AtPrime.equivQuotMaximalIdeal (𝔪 𝒪ᵥ)
      (Localization.AtPrime (𝔪 𝒪ᵥ))).toEquiv.finite_iff.mp
    exact inferInstanceAs (Finite (κ 𝒪ᵥ))
  letI : IsGaloisGroup (L ≃ₐ[Kᵥ] L) 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) :=
    finiteIntegralClosure_isGaloisGroup v L
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := L ≃ₐ[Kᵥ] L) (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ L))
  rw [finiteInertia_eq_bot_of_le_fixedField v L hL, Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx
      (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ L)) (L ≃ₐ[Kᵥ] L)] at hcard
  exact hcard.symm

/-- The image of the chosen base uniformizer is irreducible at every finite Galois level inside
the local inertia fixed field. -/
theorem finiteTameUniformizerInteger_irreducible
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (hL : L ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    Irreducible (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (tameUniformizerInteger v)) := by
  have hp : 𝔪 𝒪ᵥ ≠ ⊥ := IsDiscreteValuationRing.not_a_field 𝒪ᵥ
  have hmaple : (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L)) ≤
      𝔪 (IntegralClosure 𝒪ᵥ L) :=
    Ideal.map_le_iff_le_comap.mpr
      (le_of_eq (Ideal.LiesOver.over : 𝔪 𝒪ᵥ =
        (𝔪 (IntegralClosure 𝒪ᵥ L)).comap (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L))))
  have hramificationIdx' : (𝔪 𝒪ᵥ).ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ L)) = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ L)) hp]
    exact ramificationIdx_eq_one_of_le_fixedField v L hL
  have hnotle : ¬(𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L)) ≤
      𝔪 (IntegralClosure 𝒪ᵥ L) ^ 2 := by
    rw [← Ideal.ramificationIdx'_ne_one_iff hmaple]
    exact not_ne_iff.mpr hramificationIdx'
  have hπmem : algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (tameUniformizerInteger v) ∈
      𝔪 (IntegralClosure 𝒪ᵥ L) := by
    apply hmaple
    exact Ideal.mem_map_of_mem _ <| by
      rw [maximalIdeal_eq_span_tameUniformizerInteger v]
      exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hπmem)
  · intro a b hab
    by_contra! h
    obtain ⟨ha : a ∈ 𝔪 (IntegralClosure 𝒪ᵥ L),
      hb : b ∈ 𝔪 (IntegralClosure 𝒪ᵥ L)⟩ := h
    apply hnotle
    rw [maximalIdeal_eq_span_tameUniformizerInteger v, Ideal.map_span, Set.image_singleton]
    apply (Ideal.span_singleton_le_iff_mem
      (𝔪 (IntegralClosure 𝒪ᵥ L) ^ 2)).mpr
    rw [hab, pow_two]
    exact Ideal.mul_mem_mul ha hb

/-- At every finite Galois level inside the inertia fixed field, the base maximal ideal maps to the
unique maximal ideal of the finite integral closure. -/
theorem map_maximalIdeal_eq_maximalIdeal_of_le_fixedField
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (hL : L ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L)) =
      𝔪 (IntegralClosure 𝒪ᵥ L) := by
  rw [maximalIdeal_eq_span_tameUniformizerInteger v, Ideal.map_span, Set.image_singleton]
  exact (finiteTameUniformizerInteger_irreducible v L hL).maximalIdeal_eq.symm

/-- Finite-level factorization by the base uniformizer and a unit of the finite integral
closure. -/
theorem exists_eq_tameUniformizerInteger_zpow_mul_integralUnit
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (hL : L ≤ IntermediateField.fixedField (localInertiaGroup v))
    {u : L} (hu : u ≠ 0) :
    ∃ (m : ℤ) (a : (IntegralClosure 𝒪ᵥ L)ˣ),
      u = (algebraMap 𝒪ᵥ L (tameUniformizerInteger v)) ^ m *
        algebraMap (IntegralClosure 𝒪ᵥ L) L (a : IntegralClosure 𝒪ᵥ L) := by
  have htameIntegerNe : tameUniformizerInteger v ≠ 0 := by
    intro h
    apply tameUniformizer_ne_zero v
    exact congrArg Subtype.val h
  have htameFiniteNe :
      algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (tameUniformizerInteger v) ≠ 0 :=
    by
      intro h
      apply htameIntegerNe
      apply FaithfulSMul.algebraMap_injective 𝒪ᵥ (IntegralClosure 𝒪ᵥ L)
      simpa using h
  have hspan : 𝔪 (IntegralClosure 𝒪ᵥ L) =
      Ideal.span {algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (tameUniformizerInteger v)} := by
    rw [← map_maximalIdeal_eq_maximalIdeal_of_le_fixedField v L hL,
      maximalIdeal_eq_span_tameUniformizerInteger v, Ideal.map_span, Set.image_singleton]
  have hirreducible := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ L) (tameUniformizerInteger v))
    htameFiniteNe hspan
  obtain ⟨m, a, ha⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hirreducible hu
  refine ⟨m, a, ?_⟩
  rw [ha]
  simp only [Units.smul_def, Algebra.smul_def]
  exact mul_comm _ _

/-- Every element of the inertia fixed field lies in a finite Galois intermediate field still
contained in that fixed field. -/
theorem exists_finiteGaloisIntermediateField_le_fixedField
    {u : Kᵥᵃˡᵍ} (hu : u ∈ IntermediateField.fixedField (localInertiaGroup v)) :
    ∃ (L : FiniteGaloisIntermediateField Kᵥ (Kᵥᵃˡᵍ)) (uL : L),
      L.toIntermediateField ≤ IntermediateField.fixedField (localInertiaGroup v) ∧
      (uL : Kᵥᵃˡᵍ) = u := by
  letI : IsGalois Kᵥ (IntermediateField.fixedField (localInertiaGroup v)) :=
    fixedField_localInertia_isGalois v
  let L := FiniteGaloisIntermediateField.adjoin Kᵥ ({u} : Set (Kᵥᵃˡᵍ))
  have huL : u ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin Kᵥ ({u} : Set (Kᵥᵃˡᵍ))
      (Set.mem_singleton u)
  have hL : L.toIntermediateField ≤
      IntermediateField.fixedField (localInertiaGroup v) := by
    rw [FiniteGaloisIntermediateField.adjoin_val,
      IntermediateField.normalClosure_le_iff_of_normal,
      IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr hu
  exact ⟨L, ⟨u, huL⟩, hL, rfl⟩

/-- Every nonzero element of the local inertia fixed field is an integer power of the chosen base
uniformizer times an integral unit in that fixed field. -/
theorem fixedFieldUniformizerDecomposition :
    FixedFieldUniformizerDecomposition v := by
  intro u hu0 hu
  obtain ⟨L, uL, hL, huL⟩ :=
    exists_finiteGaloisIntermediateField_le_fixedField v hu
  have huL0 : uL ≠ 0 := by
    intro h
    apply hu0
    rw [← huL, h]
    rfl
  obtain ⟨m, a, ha⟩ :=
    exists_eq_tameUniformizerInteger_zpow_mul_integralUnit v L hL huL0
  let aTop : Kᵥᵃˡᵍ := (finiteIntegralClosureAlgHom v L
    (a : IntegralClosure 𝒪ᵥ L)).1
  have haIntegral : IsIntegral 𝒪ᵥ aTop :=
    (finiteIntegralClosureAlgHom v L (a : IntegralClosure 𝒪ᵥ L)).2
  have haInvIntegral : IsIntegral 𝒪ᵥ aTop⁻¹ := by
    let aInvTop := finiteIntegralClosureAlgHom v L
      ((a⁻¹ : (IntegralClosure 𝒪ᵥ L)ˣ) : IntegralClosure 𝒪ᵥ L)
    have hmulIC : finiteIntegralClosureAlgHom v L (a : IntegralClosure 𝒪ᵥ L) *
        aInvTop = 1 := by
      rw [← map_mul]
      simp
    have hmul :
        (finiteIntegralClosureAlgHom v L (a : IntegralClosure 𝒪ᵥ L)).1 *
          aInvTop.1 = 1 := congrArg Subtype.val hmulIC
    have haInvEq : aInvTop.1 = aTop⁻¹ :=
      (inv_eq_of_mul_eq_one_right (by simpa [aTop] using hmul)).symm
    rw [← haInvEq]
    exact aInvTop.2
  have haFixed : aTop ∈ IntermediateField.fixedField (localInertiaGroup v) := by
    change ((a : IntegralClosure 𝒪ᵥ L).1 : Kᵥᵃˡᵍ) ∈
      IntermediateField.fixedField (localInertiaGroup v)
    exact hL (a : IntegralClosure 𝒪ᵥ L).1.2
  refine ⟨m, aTop, haIntegral, haInvIntegral, haFixed, ?_⟩
  have htame : L.val (algebraMap 𝒪ᵥ L (tameUniformizerInteger v)) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v) := rfl
  have haMap : L.val
      (algebraMap (IntegralClosure 𝒪ᵥ L) L (a : IntegralClosure 𝒪ᵥ L)) = aTop := rfl
  calc
    u = (uL : Kᵥᵃˡᵍ) := huL.symm
    _ = L.val ((algebraMap 𝒪ᵥ L (tameUniformizerInteger v)) ^ m *
        algebraMap (IntegralClosure 𝒪ᵥ L) L (a : IntegralClosure 𝒪ᵥ L)) :=
      congrArg L.val ha
    _ = (L.val (algebraMap 𝒪ᵥ L (tameUniformizerInteger v))) ^ m *
        L.val (algebraMap (IntegralClosure 𝒪ᵥ L) L
          (a : IntegralClosure 𝒪ᵥ L)) := by rw [map_mul, map_zpow₀]
    _ = (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v)) ^ m * aTop := by
      rw [htame, haMap]

/-- The unconditional exact kernel theorem. -/
theorem localTameAbelianInertiaGroup_eq_ker :
    localTameAbelianInertiaGroup v =
      (tameResidueChar v).ker.map (localInertiaGroup v).subtype :=
  localTameAbelianInertiaGroup_eq_ker_of_fixedFieldUniformizerDecomposition v
    (fixedFieldUniformizerDecomposition v)
