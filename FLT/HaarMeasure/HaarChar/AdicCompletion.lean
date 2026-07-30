/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.HaarMeasure.HaarChar.Ring
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers
public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
public import FLT.NumberField.Completion.Finite
import FLT.DedekindDomain.AdicValuation

/-!
# The Haar character of an arbitrary finite completion

For the local-field mathematics, the FLT repository's `methodology/SOURCE-REGISTER.md`
entry `SRC-027` points to Voight, 29.4.1--8 and 29.6.1--3. The
quotation motivates the valuation-ring index calculation; compilation and the kernel audit, not
the quotation, prove the Lean theorem below.
-/

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Measure IsLocalRing
open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable (K : Type*) [Field K] [NumberField K]
  (v : HeightOneSpectrum (NumberField.RingOfIntegers K))

private noncomputable abbrev OO :=
  (1 : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K)).toAddSubgroup

private theorem coe_OO :
    ((OO K v : AddSubgroup (v.adicCompletion K)) : Set (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext x
  simp only [OO, Submodule.coe_toAddSubgroup, SetLike.mem_coe, Submodule.mem_one]
  exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

private theorem coe_smul_OO (pi : v.adicCompletionIntegers K) :
    (((pi : v.adicCompletion K) • OO K v : AddSubgroup (v.adicCompletion K)) :
        Set (v.adicCompletion K)) =
      (pi : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [AddSubgroup.coe_pointwise_smul, coe_OO]

private theorem meas_smul_OO (pi : v.adicCompletionIntegers K) :
    MeasurableSet (((pi : v.adicCompletion K) • OO K v : AddSubgroup (v.adicCompletion K)) :
      Set (v.adicCompletion K)) := by
  rw [coe_smul_OO]
  exact ((NumberField.isCompact_adicCompletionIntegers K v).image
    (continuous_const_mul (pi : v.adicCompletion K))).measurableSet

private theorem meas_OO :
    MeasurableSet ((OO K v : AddSubgroup (v.adicCompletion K)) : Set (v.adicCompletion K)) := by
  rw [coe_OO]
  exact (NumberField.isOpenAdicCompletionIntegers K v).measurableSet

private theorem smul_OO_le (pi : v.adicCompletionIntegers K) :
    ((pi : v.adicCompletion K) • OO K v) ≤ OO K v := by
  rw [SetLike.le_def]
  intro x hx
  rw [← SetLike.mem_coe, coe_smul_OO] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← SetLike.mem_coe, coe_OO, SetLike.mem_coe]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers, smul_eq_mul, Valuation.map_mul]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hy
  exact mul_le_one' pi.2 hy

private theorem relIndex_smul_OO (pi : v.adicCompletionIntegers K)
    (hpi : Valued.v (pi : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    ((pi : v.adicCompletion K) • OO K v).relIndex (OO K v) =
      Nat.card (ResidueField (v.adicCompletionIntegers K)) := by
  have h1 :
      (pi • (1 : Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))) =
        maximalIdeal (v.adicCompletionIntegers K) := by
    rw [HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hpi,
      Submodule.smul_one_eq_span, Ideal.submodule_span_eq]
  have step1 :
      (pi • (1 : Submodule (v.adicCompletionIntegers K)
        (v.adicCompletionIntegers K))).toAddSubgroup.index =
          Nat.card (ResidueField (v.adicCompletionIntegers K)) := by
    rw [h1]
    rfl
  rw [← AddSubgroup.relIndex_top_right] at step1
  let f : (v.adicCompletionIntegers K) →+ (v.adicCompletion K) :=
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toAddMonoidHom
  have hpres := AddSubgroup.relIndex_comap
    (H := (pi : v.adicCompletion K) • OO K v) (f := f) (K := (⊤ : AddSubgroup _))
  have map_top : AddSubgroup.map f ⊤ = OO K v := by
    ext a
    simp only [f, OO, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and,
      Submodule.mem_toAddSubgroup, Submodule.mem_one]
    rfl
  have map_H : AddSubgroup.comap f ((pi : v.adicCompletion K) • OO K v) =
      (pi • (1 : Submodule (v.adicCompletionIntegers K)
        (v.adicCompletionIntegers K))).toAddSubgroup := by
    simp only [f, OO, RingHom.toAddMonoidHom_eq_coe,
      Submodule.pointwise_smul_toAddSubgroup, ← AddSubgroup.comap_smul_one
        (v.adicCompletionIntegers K) (v.adicCompletion K)]
    rfl
  rw [map_top, map_H] at hpres
  rwa [hpres] at step1

private theorem card_residue_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv).symm

private theorem card_residue_ne_zero :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
  Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩

private theorem nnnorm_of_val_neg_one (x : v.adicCompletion K)
    (hx : Valued.v x = Multiplicative.ofAdd (-1 : ℤ)) :
    ‖x‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  rw [← NNReal.coe_inj, coe_nnnorm, NumberField.FinitePlace.norm_def, hx]
  simp [WithZeroMulInt.toNNReal, WithZero.unzero]

private theorem nnnorm_of_val_one (x : v.adicCompletion K) (hx : Valued.v x = 1) :
    ‖x‖₊ = 1 := by
  rw [← NNReal.coe_inj, coe_nnnorm, NumberField.FinitePlace.norm_def, hx]
  simp

private theorem val_inv_eq_one {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  have h := congrArg (Valued.v (R := v.adicCompletion K)) u.mul_inv
  rwa [Valuation.map_mul, hu, one_mul, map_one] at h

private theorem hchar_one_of_val_one (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : ringHaarChar u = 1 := by
  have hu' := val_inv_eq_one K v hu
  refine ringHaarChar_eq_of_measure_smul_eq_mul
    (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (μ := addHaar)
    ((NumberField.isOpenAdicCompletionIntegers K v).measure_ne_zero _ ⟨0, zero_mem _⟩)
    (NumberField.isCompact_adicCompletionIntegers K v).measure_ne_top ?_
  rw [show u • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from ?_]
  · simp
  · apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
        smul_eq_mul, Valuation.map_mul, hu, one_mul] at hy ⊢
      exact hy
    · intro x hx
      refine ⟨u⁻¹ • x, ?_, by simp [Units.smul_def, smul_eq_mul]⟩
      simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
        Units.smul_def, smul_eq_mul, Valuation.map_mul, hu', one_mul] at hx ⊢
      exact hx

private theorem ringHaarChar_uniformizer (pi : v.adicCompletionIntegers K)
    (hpi : Valued.v (pi : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ))
    (hpi0 : (pi : v.adicCompletion K) ≠ 0) :
    ringHaarChar (Units.mk0 (pi : v.adicCompletion K) hpi0) =
      (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ≥0)⁻¹ := by
  have hq0 : Nat.card (ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    card_residue_ne_zero K v
  haveI : ((pi : v.adicCompletion K) • OO K v).IsFiniteRelIndex (OO K v) :=
    ⟨by rw [relIndex_smul_OO K v pi hpi]; exact hq0⟩
  have key := index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup
    (smul_OO_le K v pi) (meas_smul_OO K v pi) (meas_OO K v)
      (addHaar : Measure (v.adicCompletion K))
  rw [relIndex_smul_OO K v pi hpi] at key
  refine ringHaarChar_eq_of_measure_smul_eq_mul
    (s := ((OO K v : AddSubgroup (v.adicCompletion K)) : Set (v.adicCompletion K)))
    (μ := addHaar) ?_ ?_ ?_
  · rw [coe_OO]
    exact (NumberField.isOpenAdicCompletionIntegers K v).measure_ne_zero _ ⟨0, zero_mem _⟩
  · rw [coe_OO]
    exact (NumberField.isCompact_adicCompletionIntegers K v).measure_ne_top
  · have hsmulset : (Units.mk0 (pi : v.adicCompletion K) hpi0) •
        ((OO K v : AddSubgroup (v.adicCompletion K)) : Set (v.adicCompletion K)) =
        (((pi : v.adicCompletion K) • OO K v : AddSubgroup (v.adicCompletion K)) :
          Set (v.adicCompletion K)) := by
      rw [AddSubgroup.coe_pointwise_smul]
      ext x
      simp [Units.smul_def]
    rw [hsmulset, ← key, ← mul_assoc, ENNReal.coe_inv (by exact_mod_cast hq0)]
    rw [show ((Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ≥0) : ℝ≥0∞) =
      (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ≥0∞) by simp]
    rw [ENNReal.inv_mul_cancel (by exact_mod_cast hq0) (by simp), one_mul]

end MeasureTheory

theorem MeasureTheory.ringHaarChar_adicCompletion
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (v.adicCompletion K)ˣ) :
    ringHaarChar u = ‖(u : v.adicCompletion K)‖₊ := by
  obtain ⟨pi, hpi⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  have hpi0 : (pi : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hpi
    exact WithZero.zero_ne_coe hpi
  set P : (v.adicCompletion K)ˣ := Units.mk0 (pi : v.adicCompletion K) hpi0 with hP
  have hPv : Valued.v (P : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) := hpi
  have hbase : ringHaarChar P = ‖(P : v.adicCompletion K)‖₊ := by
    rw [hP, MeasureTheory.ringHaarChar_uniformizer K v pi hpi hpi0,
      MeasureTheory.card_residue_eq_absNorm K v]
    exact (MeasureTheory.nnnorm_of_val_neg_one K v _ hpi).symm
  have hu0 : Valued.v (u : v.adicCompletion K) ≠ 0 := by simp
  obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ,
      Valued.v (u : v.adicCompletion K) = (↑m : WithZero (Multiplicative ℤ)) :=
    ⟨WithZero.unzero hu0, (WithZero.coe_unzero hu0).symm⟩
  set n : ℤ := -Multiplicative.toAdd m with hn
  have hvPn : Valued.v ((P ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      Valued.v (u : v.adicCompletion K) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hPv, ← WithZero.coe_zpow,
      ← Int.ofAdd_mul, hn, hm]
    congr 1
    simp
  set k : (v.adicCompletion K)ˣ := u * (P ^ n)⁻¹ with hk
  have hkv : Valued.v (k : v.adicCompletion K) = 1 := by
    have hinv : Valued.v (((P ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (Valued.v ((P ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹ := by
      have h := congrArg (Valued.v (R := v.adicCompletion K)) (P ^ n).mul_inv
      rw [Valuation.map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h)
    rw [hk, Units.val_mul, Valuation.map_mul, hinv, hvPn]
    exact mul_inv_cancel₀ hu0
  have hdecomp : u = P ^ n * k := by
    rw [hk, ← mul_assoc, mul_comm (P ^ n) u, mul_assoc]
    simp
  rw [hdecomp, map_mul, MeasureTheory.hchar_one_of_val_one K v k hkv, mul_one, map_zpow,
    hbase, Units.val_mul, nnnorm_mul, MeasureTheory.nnnorm_of_val_one K v _ hkv, mul_one,
    Units.val_zpow_eq_zpow_val, nnnorm_zpow]
