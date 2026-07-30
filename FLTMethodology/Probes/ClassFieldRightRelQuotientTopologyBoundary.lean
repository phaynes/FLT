/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdeleRing
import FLT.PotentialModularity.ClassField.FujisakiScalarExtension
import FLT.PotentialModularity.ClassField.IdelicModuleComparison

/-!
# Class-field right-relation quotient topology boundary probe

This methodology-only file records the analytic-free compactness chain from Fujisaki's right-coset
quotient through inversion, scalar extension, Haar-kernel restriction, and the diagonal comparison.
The resulting named value concerns the repository ring-Haar-character kernel quotient only.

It does not identify `ringHaarChar` with `ideleModule`, identify their kernels, establish
compactness of either retained norm-one target, or close a parent Class Field obligation.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace FLT.PotentialModularity.ClassField

section RightRelRepresentatives

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
variable (H : Subgroup G) (g : G)

example :
    QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel H
        (Quotient.mk (QuotientGroup.rightRel H) g) =
      (QuotientGroup.mk g⁻¹ : G ⧸ H) := rfl

example :
    (QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel H).symm
        (QuotientGroup.mk g : G ⧸ H) =
      Quotient.mk (QuotientGroup.rightRel H) g⁻¹ := rfl

example : True := by
  fail_if_success
    exact (rfl :
      QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel H
          (Quotient.mk (QuotientGroup.rightRel H) g) =
        (QuotientGroup.mk g : G ⧸ H))
  trivial

end RightRelRepresentatives

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : True := by
  fail_if_success
    letI : Group (Quotient (QuotientGroup.rightRel H)) := inferInstance
  trivial

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def scalarExtensionContinuousMulEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ* AdeleRing (𝓞 K) K where
  __ := (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv.toMulEquiv
  continuous_toFun := (adeleScalarExtensionContinuousAlgEquiv K).continuous_toFun
  continuous_invFun := (adeleScalarExtensionContinuousAlgEquiv K).continuous_invFun

private noncomputable def scalarExtensionUnitsContinuousMulEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K)ˣ ≃ₜ* (AdeleRing (𝓞 K) K)ˣ :=
  Units.mapContinuousMulEquiv (scalarExtensionContinuousMulEquiv K)

private noncomputable def scalarExtensionContinuousZAlgEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K) ≃A[ℤ] AdeleRing (𝓞 K) K := by
  letI : IsBiscalar K ℤ (adeleScalarExtensionContinuousAlgEquiv K).toAlgHom :=
    { map_smul₁ := fun r a =>
        map_smul (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv r a
      map_smul₂ := fun n a =>
        map_zsmul (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv n a }
  exact (adeleScalarExtensionContinuousAlgEquiv K).changeScalars ℤ

private theorem scalarExtension_ringHaarChar
    (r : (K ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    ringHaarChar r = ringHaarChar (scalarExtensionUnitsContinuousMulEquiv K r) :=
  ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv
    (scalarExtensionContinuousZAlgEquiv K) r

private theorem scalarExtension_mem_ringHaarCharKer
    (x : (K ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    x ∈ ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ↔
      scalarExtensionUnitsContinuousMulEquiv K x ∈
        ringHaarCharKer (AdeleRing (𝓞 K) K) := by
  rw [mem_ringHaarChar_ker, mem_ringHaarChar_ker, scalarExtension_ringHaarChar]

private theorem scalarExtension_symm_mem_ringHaarCharKer
    (y : (AdeleRing (𝓞 K) K)ˣ) :
    (scalarExtensionUnitsContinuousMulEquiv K).symm y ∈
        ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ↔
      y ∈ ringHaarCharKer (AdeleRing (𝓞 K) K) := by
  rw [scalarExtension_mem_ringHaarCharKer]
  simp

private noncomputable def scalarExtensionRingHaarKerMulEquiv :
    ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ≃*
      ringHaarCharKer (AdeleRing (𝓞 K) K) where
  toFun x :=
    ⟨scalarExtensionUnitsContinuousMulEquiv K x,
      (scalarExtension_mem_ringHaarCharKer K x).mp x.2⟩
  invFun y :=
    ⟨(scalarExtensionUnitsContinuousMulEquiv K).symm y,
      (scalarExtension_symm_mem_ringHaarCharKer K y).mpr y.2⟩
  left_inv := fun x => Subtype.ext (by simp)
  right_inv := fun y => Subtype.ext (by simp)
  map_mul' := fun x y => Subtype.ext (by simp)

/-- The retained scalar-extension unit equivalence restricted to the two ring-Haar-character
kernels. -/
noncomputable def scalarExtensionRingHaarKerContinuousMulEquiv :
    ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ*
      ringHaarCharKer (AdeleRing (𝓞 K) K) where
  __ := scalarExtensionRingHaarKerMulEquiv K
  continuous_toFun :=
    Continuous.subtype_mk
      ((scalarExtensionUnitsContinuousMulEquiv K).continuous.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      ((scalarExtensionUnitsContinuousMulEquiv K).symm.continuous.comp continuous_subtype_val) _

private theorem scalarExtensionUnits_map_incl (x : Kˣ) :
    scalarExtensionUnitsContinuousMulEquiv K
        (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K x) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x := by
  apply Units.ext
  change
    (Algebra.TensorProduct.lid K (AdeleRing (𝓞 K) K)) ((x : K) ⊗ₜ[K] 1) = _
  rw [Algebra.TensorProduct.lid_tmul, Algebra.smul_def, mul_one]
  rfl

/-- The scalar-extension Haar-kernel equivalence maps the Fujisaki source diagonal to the
repository principal-idele comap inside the target Haar kernel. -/
theorem scalarExtensionRingHaarKer_map_diagonal :
    Subgroup.map (scalarExtensionRingHaarKerContinuousMulEquiv K).toMonoidHom
        (Subgroup.comap (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range) =
      Subgroup.comap (ringHaarCharKer (AdeleRing (𝓞 K) K)).subtype
        (principalIdeles K) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype,
    principalIdeles, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    refine ⟨k, ?_⟩
    rw [show (((scalarExtensionRingHaarKerContinuousMulEquiv K).toMonoidHom x :
        ringHaarCharKer (AdeleRing (𝓞 K) K)) : (AdeleRing (𝓞 K) K)ˣ) =
      scalarExtensionUnitsContinuousMulEquiv K x from rfl, ← hk,
      scalarExtensionUnits_map_incl]
  · rintro ⟨k, hk⟩
    refine
      ⟨⟨(scalarExtensionUnitsContinuousMulEquiv K).symm y,
          (scalarExtension_symm_mem_ringHaarCharKer K y).mpr y.2⟩,
        ⟨k, ?_⟩, ?_⟩
    · exact ((ContinuousMulEquiv.symm_apply_eq
        (scalarExtensionUnitsContinuousMulEquiv K)).mpr
          (by rw [scalarExtensionUnits_map_incl, hk])).symm
    · apply Subtype.ext
      change
        scalarExtensionUnitsContinuousMulEquiv K
            ((scalarExtensionUnitsContinuousMulEquiv K).symm
              (y : (AdeleRing (𝓞 K) K)ˣ)) =
          (y : (AdeleRing (𝓞 K) K)ˣ)
      simp

example :
    CompactSpace
      (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ⧸
        Subgroup.comap
          (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range) := by
  letI : CompactSpace
      (Quotient (QuotientGroup.rightRel
        (Subgroup.comap (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range))) :=
    NumberField.AdeleRing.DivisionAlgebra.compact_quotient K K
  exact (QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel _).compactSpace

noncomputable example :
    ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ*
      ringHaarCharKer (AdeleRing (𝓞 K) K) :=
  scalarExtensionRingHaarKerContinuousMulEquiv K

example :
    Subgroup.map (scalarExtensionRingHaarKerContinuousMulEquiv K).toMonoidHom
        (Subgroup.comap (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range) =
      Subgroup.comap (ringHaarCharKer (AdeleRing (𝓞 K) K)).subtype
        (principalIdeles K) :=
  scalarExtensionRingHaarKer_map_diagonal K

/-- Fujisaki compactness transported through the analytic-free chain to the repository
ring-Haar-character-kernel quotient by principal ideles. This is not compactness of a retained
norm-one target. -/
theorem compactSpace_ringHaarCharKer_quotient_principalIdeles :
    CompactSpace
      (ringHaarCharKer (AdeleRing (𝓞 K) K) ⧸
        Subgroup.comap
          (ringHaarCharKer (AdeleRing (𝓞 K) K)).subtype
          (principalIdeles K)) := by
  letI : IsMulCommutative ((K ⊗[K] AdeleRing (𝓞 K) K)ˣ) :=
    ⟨⟨fun a b => Units.ext (mul_comm (a : K ⊗[K] AdeleRing (𝓞 K) K) b)⟩⟩
  letI : CompactSpace
      (Quotient (QuotientGroup.rightRel
        (Subgroup.comap (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range))) :=
    NumberField.AdeleRing.DivisionAlgebra.compact_quotient K K
  letI : CompactSpace
      (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K) ⧸
        Subgroup.comap
          (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
          (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range) :=
    (QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel _).compactSpace
  exact
    (QuotientGroup.continuousMulEquiv _ _
      (scalarExtensionRingHaarKerContinuousMulEquiv K)
      (scalarExtensionRingHaarKer_map_diagonal K)).toHomeomorph.compactSpace

example : CompactSpace
    (ringHaarCharKer (AdeleRing (𝓞 K) K) ⧸
      Subgroup.comap
        (ringHaarCharKer (AdeleRing (𝓞 K) K)).subtype
        (principalIdeles K)) :=
  compactSpace_ringHaarCharKer_quotient_principalIdeles K

example
    (h : ringHaarCharKer (AdeleRing (𝓞 K) K) = NormOneIdeles K) :
    CompactSpace (NormOneIdeleClassGroup K) := by
  have hc := compactSpace_ringHaarCharKer_quotient_principalIdeles K
  rw [h] at hc
  exact hc

/- The two retained norm-one compactness targets remain unavailable. -/

/--
error: failed to synthesize
  CompactSpace (NormOneIdeleClassGroup K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassGroup K)

/--
error: failed to synthesize
  CompactSpace ↥(NormOneIdeleClassKernel K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassKernel K)

example (_x : (AdeleRing (𝓞 K) K)ˣ) : True := by
  fail_if_success
    exact (rfl : ringHaarChar _x = ((ideleModule K _x : NNRealˣ) : NNReal))
  fail_if_success
    solve
    | suffices ringHaarChar _x = ((ideleModule K _x : NNRealˣ) : NNReal) by trivial
      simp
  trivial

example : True := by
  fail_if_success
    exact (rfl : ringHaarCharKer (AdeleRing (𝓞 K) K) = NormOneIdeles K)
  fail_if_success
    solve
    | suffices ringHaarCharKer (AdeleRing (𝓞 K) K) = NormOneIdeles K by trivial
      simp
  trivial

example : True := by
  fail_if_success
    exact (rfl :
      (ringHaarCharKer (AdeleRing (𝓞 K) K) ⧸
        Subgroup.comap
          (ringHaarCharKer (AdeleRing (𝓞 K) K)).subtype
          (principalIdeles K)) =
        NormOneIdeleClassGroup K)
  trivial

#print axioms scalarExtensionContinuousMulEquiv
#print axioms scalarExtensionUnitsContinuousMulEquiv
#print axioms scalarExtensionContinuousZAlgEquiv
#print axioms scalarExtension_ringHaarChar
#print axioms scalarExtension_mem_ringHaarCharKer
#print axioms scalarExtension_symm_mem_ringHaarCharKer
#print axioms scalarExtensionRingHaarKerMulEquiv
#print axioms scalarExtensionRingHaarKerContinuousMulEquiv
#print axioms scalarExtensionUnits_map_incl
#print axioms scalarExtensionRingHaarKer_map_diagonal
#print axioms compactSpace_ringHaarCharKer_quotient_principalIdeles

end FLT.PotentialModularity.ClassField

#print axioms QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel
#print axioms QuotientAddGroup.quotientRightRelHomeomorphQuotientLeftRel
