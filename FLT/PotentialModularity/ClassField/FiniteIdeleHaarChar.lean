/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.HaarMeasure.HaarChar.AdicCompletion
public import FLT.PotentialModularity.ClassField.IdelicModule
import FLT.NumberField.HeightOneSpectrum

/-!
# Finite-idele Haar character comparison

This module compares the additive Haar character of the finite adele ring with the
normalized finite idelic module. No archimedean or global comparison is made here.
-/

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open scoped RestrictedProduct NNReal

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- The local Haar character at a place equals the normalized local idele factor. -/
private theorem ringHaarChar_eq_finiteIdeleFactor
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ringHaarChar ((MulEquiv.restrictedProductUnits a) v) =
      ((finiteIdeleFactor K a v : NNRealˣ) : NNReal) := by
  rw [MeasureTheory.ringHaarChar_adicCompletion]
  rfl

/-- The finite-adele Haar character factors as a finproduct over the finite places. -/
private theorem ringHaarChar_finiteAdeleRing_eq_finprod
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ringHaarChar a =
      ∏ᶠ v, ringHaarChar ((MulEquiv.restrictedProductUnits a) v) := by
  letI := Fact.mk <| NumberField.isOpenAdicCompletionIntegers K
  letI := NumberField.instCompactSpaceAdicCompletionIntegers K
  exact MeasureTheory.ringHaarChar_restrictedProduct a

/-- The finite-adele ring Haar character is the normalized finite idelic module. -/
theorem ringHaarChar_finiteAdeleRing_eq_finiteIdeleModule
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ringHaarChar a = ((finiteIdeleModule K a : NNRealˣ) : NNReal) := by
  calc
    ringHaarChar a =
        ∏ᶠ v, ringHaarChar ((MulEquiv.restrictedProductUnits a) v) :=
      ringHaarChar_finiteAdeleRing_eq_finprod K a
    _ = (Units.coeHom NNReal) (∏ᶠ v, finiteIdeleFactor K a v) := by
      rw [MonoidHom.map_finprod _ (finiteIdeleFactor_hasFiniteMulSupport K a)]
      apply finprod_congr
      intro v
      exact ringHaarChar_eq_finiteIdeleFactor K a v
    _ = ((finiteIdeleModule K a : NNRealˣ) : NNReal) := rfl

end FLT.PotentialModularity.ClassField
