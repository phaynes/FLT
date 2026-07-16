/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FLT.KnownIn1980s.EllipticCurves.TateCurve
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Tate discriminant formal-route methodology probe

This independent methodology probe is outside the verified FLT root. It records the
kernel-checked algebraic and modular-form side of the Tate discriminant comparison and
states the exact remaining formal-product/q-expansion bridge. It is not imported by the
upstream FLT proof.
-/

open scoped ArithmeticFunction.sigma
open PowerSeries
open MatrixGroups
open ModularForm ModularFormClass

namespace TateCurveRouteProbe

noncomputable def c₆Formal : ℤ⟦X⟧ := 1 - 504 * TateCurve.sInt 5

private theorem twelve_dvd_five_sigma_three_add_seven_sigma_five (m : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 m : ℤ) +
      7 * (ArithmeticFunction.sigma 5 m : ℤ) := by
  have h12 : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  have hσ : ∑ d ∈ m.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) =
      5 * (ArithmeticFunction.sigma 3 m : ℤ) +
        7 * (ArithmeticFunction.sigma 5 m : ℤ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
    push_cast
    ring
  rw [← hσ]
  exact Finset.dvd_sum fun d _ ↦ h12 d

theorem c₆Formal_eq_one_sub_mul_a₄Formal_add_mul_a₆Formal :
    c₆Formal = 1 - 72 * TateCurve.a₄Formal + 864 * TateCurve.a₆Formal := by
  ext m
  rw [show (72 : ℤ⟦X⟧) = PowerSeries.C 72 by norm_num,
    show (864 : ℤ⟦X⟧) = PowerSeries.C 864 by norm_num]
  simp only [map_add, map_sub, map_one]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    TateCurve.coeff_a₄Formal, TateCurve.coeff_a₆Formal]
  simp only [c₆Formal]
  rw [show (504 : ℤ⟦X⟧) = PowerSeries.C 504 by norm_num]
  simp only [map_sub, map_one]
  rw [
    PowerSeries.coeff_C_mul, TateCurve.sInt, PowerSeries.coeff_mk]
  have hdiv := twelve_dvd_five_sigma_three_add_seven_sigma_five m
  have hcancel := Int.ediv_mul_cancel hdiv
  linear_combination 72 * hcancel

theorem mul_weierstrassDiscriminantFormal_eq_c₄_cube_sub_c₆_sq :
    (1728 : ℤ⟦X⟧) * TateCurve.weierstrassDiscriminantFormal =
      TateCurve.c₄Formal ^ 3 - c₆Formal ^ 2 := by
  rw [TateCurve.c₄Formal_eq_one_sub_mul_a₄Formal,
    c₆Formal_eq_one_sub_mul_a₄Formal_add_mul_a₆Formal]
  simp only [TateCurve.weierstrassDiscriminantFormal]
  ring

theorem map_c₄Formal_eq_qExpansion_E₄ :
    PowerSeries.map (Int.castRingHom ℂ) TateCurve.c₄Formal =
      UpperHalfPlane.qExpansion 1 ModularForm.E₄ := by
  ext m
  rw [PowerSeries.coeff_map,
    EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩]
  simp [TateCurve.c₄Formal, TateCurve.sInt,
    show bernoulli 4 = -1 / 30 by decide +kernel]
  split <;> rename_i hm
  · subst m
    norm_num
  · push_cast
    rw [show (240 : ℤ⟦X⟧) = PowerSeries.C 240 by norm_num,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    norm_num

theorem map_c₆Formal_eq_qExpansion_E₆ :
    PowerSeries.map (Int.castRingHom ℂ) c₆Formal =
      UpperHalfPlane.qExpansion 1 ModularForm.E₆ := by
  ext m
  rw [PowerSeries.coeff_map,
    EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩]
  simp [c₆Formal, TateCurve.sInt,
    show bernoulli 6 = 1 / 42 by decide +kernel]
  split <;> rename_i hm
  · subst m
    norm_num
  · push_cast
    rw [show (504 : ℤ⟦X⟧) = PowerSeries.C 504 by norm_num,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    norm_num

noncomputable def e₄CubeSubE₆SqForm :
    ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (ModularForm.E₄.pow 3) -
    ModularForm.mcast (by decide) (ModularForm.E₆.pow 2)

theorem e₄CubeSubE₆SqForm_apply (z : UpperHalfPlane) :
    e₄CubeSubE₆SqForm z = ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2 := by
  simp only [e₄CubeSubE₆SqForm, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]

theorem qExpansion_e₄CubeSubE₆SqForm :
    UpperHalfPlane.qExpansion 1 e₄CubeSubE₆SqForm =
      UpperHalfPlane.qExpansion 1 ModularForm.E₄ ^ 3 -
        UpperHalfPlane.qExpansion 1 ModularForm.E₆ ^ 2 := by
  simp only [e₄CubeSubE₆SqForm, coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem qExpansion_discriminant_mul_1728_eq_E₄_cube_sub_E₆_sq :
    (1728 : ℂ) • UpperHalfPlane.qExpansion 1 CuspForm.discriminant =
      UpperHalfPlane.qExpansion 1 ModularForm.E₄ ^ 3 -
        UpperHalfPlane.qExpansion 1 ModularForm.E₆ ^ 2 := by
  have hmod :
      (1728 : ℂ) • ModularFormClass.modularForm CuspForm.discriminant =
        e₄CubeSubE₆SqForm := by
    ext z
    rw [e₄CubeSubE₆SqForm_apply]
    change 1728 * ModularForm.discriminant z = _
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    field_simp
  have hq := congrArg
    (fun f : ModularForm 𝒮ℒ 12 ↦
      UpperHalfPlane.qExpansion 1 f) hmod
  rw [← qExpansion_e₄CubeSubE₆SqForm]
  change UpperHalfPlane.qExpansion 1
    ((1728 : ℂ) • (CuspForm.discriminant : UpperHalfPlane → ℂ)) = _ at hq
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL] at hq
  exact hq

theorem map_weierstrassDiscriminantFormal_eq_qExpansion_discriminant :
    PowerSeries.map (Int.castRingHom ℂ) TateCurve.weierstrassDiscriminantFormal =
      UpperHalfPlane.qExpansion 1 CuspForm.discriminant := by
  have hformal := congrArg (PowerSeries.map (Int.castRingHom ℂ))
    mul_weierstrassDiscriminantFormal_eq_c₄_cube_sub_c₆_sq
  have hformal' :
      (1728 : ℂ) •
          PowerSeries.map (Int.castRingHom ℂ) TateCurve.weierstrassDiscriminantFormal =
        UpperHalfPlane.qExpansion 1 ModularForm.E₄ ^ 3 -
          UpperHalfPlane.qExpansion 1 ModularForm.E₆ ^ 2 := by
    rw [show (1728 : ℤ⟦X⟧) = PowerSeries.C 1728 by norm_num] at hformal
    simp only [map_mul, map_sub, map_pow, PowerSeries.map_C] at hformal
    norm_num at hformal
    rw [map_c₄Formal_eq_qExpansion_E₄,
      map_c₆Formal_eq_qExpansion_E₆] at hformal
    rw [PowerSeries.smul_eq_C_mul]
    exact hformal
  have hscaled :
      (1728 : ℂ) •
          PowerSeries.map (Int.castRingHom ℂ) TateCurve.weierstrassDiscriminantFormal =
        (1728 : ℂ) • UpperHalfPlane.qExpansion 1 CuspForm.discriminant :=
    hformal'.trans qExpansion_discriminant_mul_1728_eq_E₄_cube_sub_E₆_sq.symm
  ext m
  have hm := congrArg (PowerSeries.coeff m) hscaled
  simp only [PowerSeries.coeff_smul, smul_eq_mul] at hm
  change
    (PowerSeries.map (Int.castRingHom ℂ) TateCurve.weierstrassDiscriminantFormal)
        (Finsupp.single () m) =
      (UpperHalfPlane.qExpansion 1 CuspForm.discriminant) (Finsupp.single () m)
  exact mul_left_cancel₀ (a := (1728 : ℂ)) (by norm_num) hm

/-- Exact remaining bridge after the algebraic/Eisenstein side has been discharged. -/
def formalProductQExpansionBridge : Prop :=
  PowerSeries.map (Int.castRingHom ℂ) TateCurve.ΔFormal =
    UpperHalfPlane.qExpansion 1 CuspForm.discriminant

#check formalProductQExpansionBridge

theorem weierstrassDiscriminantFormal_eq_deltaFormal_of_bridge
    (hΔ : formalProductQExpansionBridge) :
    TateCurve.weierstrassDiscriminantFormal = TateCurve.ΔFormal := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_weierstrassDiscriminantFormal_eq_qExpansion_discriminant]
  exact hΔ.symm

#print axioms c₆Formal_eq_one_sub_mul_a₄Formal_add_mul_a₆Formal
#print axioms mul_weierstrassDiscriminantFormal_eq_c₄_cube_sub_c₆_sq
#print axioms map_c₄Formal_eq_qExpansion_E₄
#print axioms map_c₆Formal_eq_qExpansion_E₆
#print axioms qExpansion_discriminant_mul_1728_eq_E₄_cube_sub_E₆_sq
#print axioms map_weierstrassDiscriminantFormal_eq_qExpansion_discriminant
#print axioms weierstrassDiscriminantFormal_eq_deltaFormal_of_bridge

end TateCurveRouteProbe
