/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdeleRing
import FLT.PotentialModularity.ClassField.FujisakiScalarExtension
import FLT.PotentialModularity.ClassField.IdelicModuleComparison

/-!
# Class-field Fujisaki scalar-extension boundary probe

This methodology-only file consumes the Lean-internal comparison required by the scalar-extension
presentation in `Finiteness.lean`. Voight presents adeles as a restricted direct product and uses
scalar extension for the division algebra.

The probe checks the induced unit and diagonal comparisons and the ring-Haar-character transport
adapter. It does not identify `ringHaarChar` with `ideleModule`, identify their norm-one kernels, or
establish compactness of either retained norm-one target.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def scalarExtensionContinuousMulEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ* AdeleRing (𝓞 K) K where
  __ := (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv.toMulEquiv
  continuous_toFun := (adeleScalarExtensionContinuousAlgEquiv K).continuous_toFun
  continuous_invFun := (adeleScalarExtensionContinuousAlgEquiv K).continuous_invFun

private noncomputable def scalarExtensionUnitsContinuousMulEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K)ˣ ≃ₜ* (AdeleRing (𝓞 K) K)ˣ :=
  Units.mapContinuousMulEquiv (scalarExtensionContinuousMulEquiv K)

noncomputable example :
    (K ⊗[K] AdeleRing (𝓞 K) K)ˣ ≃ₜ* (AdeleRing (𝓞 K) K)ˣ :=
  scalarExtensionUnitsContinuousMulEquiv K

example (x : Kˣ) :
    scalarExtensionUnitsContinuousMulEquiv K
        (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K x) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x := by
  fail_if_success rfl
  apply Units.ext
  change (Algebra.TensorProduct.lid K (AdeleRing (𝓞 K) K)) ((x : K) ⊗ₜ[K] 1) = _
  rw [Algebra.TensorProduct.lid_tmul, Algebra.smul_def, mul_one]
  rfl

private noncomputable def scalarExtensionContinuousZAlgEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K) ≃A[ℤ] AdeleRing (𝓞 K) K := by
  letI : IsBiscalar K ℤ (adeleScalarExtensionContinuousAlgEquiv K).toAlgHom :=
    { map_smul₁ := fun r a =>
        map_smul (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv r a
      map_smul₂ := fun n a =>
        map_zsmul (adeleScalarExtensionContinuousAlgEquiv K).toAlgEquiv n a }
  exact (adeleScalarExtensionContinuousAlgEquiv K).changeScalars ℤ

example (r : (K ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    ringHaarChar r =
      ringHaarChar
        (Units.map (scalarExtensionContinuousZAlgEquiv K).toMulEquiv.toMonoidHom r) :=
  ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv
    (scalarExtensionContinuousZAlgEquiv K) r

example : CompactSpace
    (Quotient (QuotientGroup.rightRel
      (Subgroup.comap (ringHaarCharKer (K ⊗[K] AdeleRing (𝓞 K) K)).subtype
        (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K K).range))) :=
  NumberField.AdeleRing.DivisionAlgebra.compact_quotient K K

#synth T3Space (NormOneIdeleClassGroup K)

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

end FLT.PotentialModularity.ClassField

#print axioms
  FLT.PotentialModularity.ClassField.adeleScalarExtensionContinuousAlgEquiv
