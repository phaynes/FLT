/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FLTMethodology.Probes.TateDeltaFormalRoute
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Tate discriminant analytic-bridge methodology probe

This file closes the formal-product/q-expansion boundary isolated by
`TateDeltaFormalRoute`. It remains outside the verified FLT root: the declarations here
are kernel-backed methodology evidence and are not imported by the upstream proof.
-/

open Filter Set Complex
open scoped Topology
open scoped PowerSeries.WithPiTopology

namespace TateDeltaAnalyticBridgeProbe

noncomputable def partialPoly (N : ℕ) : Polynomial ℂ :=
  ∏ n ∈ Finset.range N, (1 - Polynomial.X ^ (n + 1))

theorem iteratedDeriv_eval_zero (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun q : ℂ ↦ p.eval q) 0 = k.factorial * p.coeff k := by
  have heval : (fun q : ℂ ↦ p.eval q) =
      ∑ i ∈ p.support, fun q : ℂ ↦ p.coeff i * q ^ i := by
    funext q
    simp [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [heval, iteratedDeriv_sum]
  · have hterm (i : ℕ) :
        iteratedDeriv k (fun q : ℂ ↦ p.coeff i * q ^ i) 0 =
          p.coeff i * (if k = i then i.factorial else 0) := by
      rw [iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_fun_pow_zero]
    simp_rw [hterm]
    by_cases hk : k ∈ p.support
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b hb hbk
        simp [hbk.symm]
      · exact fun h ↦ (h hk).elim
    · rw [Finset.sum_eq_zero]
      · simp [Polynomial.notMem_support_iff.mp hk]
      · intro b hb
        by_cases hbk : k = b
        · subst b
          exact (hk hb).elim
        · simp [hbk]
  · intro i hi
    fun_prop

theorem partialPoly_eval (N : ℕ) (q : ℂ) :
    (partialPoly N).eval q = ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) := by
  rw [partialPoly, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro n hn
  simp

theorem coeff_partialPoly (N k : ℕ) :
    (partialPoly N).coeff k =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
  have hcoe : ((partialPoly N : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ n ∈ Finset.range N,
        ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) := by
    change Polynomial.coeToPowerSeries.ringHom
        (∏ n ∈ Finset.range N,
          ((1 : Polynomial ℂ) - Polynomial.X ^ (n + 1))) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro n hn
    simp
  rw [← Polynomial.coeff_coe]
  exact congrArg (PowerSeries.coeff k) hcoe

theorem iteratedDeriv_partialProduct_zero (N k : ℕ) :
    iteratedDeriv k
        (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) 0 =
      k.factorial * PowerSeries.coeff k
        (∏ n ∈ Finset.range N,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
  have hfun :
      (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) =
        fun q : ℂ ↦ (partialPoly N).eval q := by
    funext q
    exact (partialPoly_eval N q).symm
  rw [hfun]
  exact (iteratedDeriv_eval_zero (partialPoly N) k).trans
    (congrArg ((k.factorial : ℂ) * ·) (coeff_partialPoly N k))

theorem tendstoLocallyUniformlyOn_iteratedDeriv_partialProduct (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ ↦ iteratedDeriv k
        (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))))
      (iteratedDeriv k (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))))
      atTop (Metric.ball 0 1) := by
  induction k with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
          |>.tendstoLocallyUniformlyOn_finsetRange
  | succ k ih =>
      have hdiff : ∀ᶠ N : ℕ in atTop,
          DifferentiableOn ℂ
            (iteratedDeriv k
              (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))))
            (Metric.ball 0 1) := by
        filter_upwards with N
        exact ((show ContDiff ℂ (k + 1)
            (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) by
          fun_prop).differentiable_iteratedDeriv' k).differentiableOn
      simpa only [Function.comp_def, iteratedDeriv_succ] using
        ih.deriv hdiff Metric.isOpen_ball

theorem coeff_prod_range_eq_tprod_of_le {k N : ℕ} (hkN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range N,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) =
      PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
  have hs : Finset.range k ⊆ Finset.range N := Finset.range_mono hkN
  calc
    PowerSeries.coeff k
        (∏ n ∈ Finset.range N,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) =
        PowerSeries.coeff k
          (∏ n ∈ Finset.range k,
            ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
      rw [← Finset.prod_sdiff hs, mul_comm]
      simpa only using
        (PowerSeries.coeff_mul_prod_one_sub_of_lt_order k
          (Finset.range N \ Finset.range k)
          (∏ n ∈ Finset.range k,
            ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)))
          (fun i ↦ (PowerSeries.X ^ (i + 1) : PowerSeries ℂ)) (by
            intro i hi
            have hik : k ≤ i := by
              exact Nat.le_of_not_gt ((Finset.mem_sdiff.mp hi).2 ∘ Finset.mem_range.mpr)
            rw [PowerSeries.order_X_pow]
            exact_mod_cast Nat.lt_add_one_of_le hik))
    _ = PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) :=
      (TateCurveRouteProbe.coeff_tprod_one_sub_X_pow_eq_prod_range ℂ k).symm

theorem iteratedDeriv_tprod_one_sub_pow_zero (k : ℕ) :
    iteratedDeriv k (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) 0 =
      k.factorial * PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
  have hlim :=
    (tendstoLocallyUniformlyOn_iteratedDeriv_partialProduct k).tendsto_at
      (show (0 : ℂ) ∈ Metric.ball 0 1 by simp)
  have hevent : ∀ᶠ N : ℕ in atTop,
      iteratedDeriv k
          (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) 0 =
        k.factorial * PowerSeries.coeff k
          (∏' n : ℕ,
            ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) := by
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [iteratedDeriv_partialProduct_zero, coeff_prod_range_eq_tprod_of_le hN]
  have hconst : Tendsto
      (fun _N : ℕ ↦ (k.factorial : ℂ) * PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))))
      atTop
      (nhds ((k.factorial : ℂ) * PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))))) := tendsto_const_nhds
  have hevent' :
      (fun _N : ℕ ↦ (k.factorial : ℂ) * PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)))) =ᶠ[atTop]
        (fun N : ℕ ↦ iteratedDeriv k
          (fun q : ℂ ↦ ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) 0) := by
    filter_upwards [hevent] with N hN
    exact hN.symm
  exact tendsto_nhds_unique hlim (hconst.congr' hevent')

theorem coeff_tprod_one_sub_pow_eq_factorial_inv_mul_iteratedDeriv (k : ℕ) :
    PowerSeries.coeff k
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) =
      (k.factorial : ℂ)⁻¹ *
        iteratedDeriv k (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) 0 := by
  rw [iteratedDeriv_tprod_one_sub_pow_zero]
  have hf : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]

noncomputable def taylorSeries (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦ (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0

@[simp]
theorem coeff_taylorSeries (f : ℂ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (taylorSeries f) =
      (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0 := by
  simp [taylorSeries]

theorem taylorSeries_mul {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f * g) = taylorSeries f * taylorSeries g := by
  ext n
  simp only [coeff_taylorSeries,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

theorem taylorSeries_one : taylorSeries (1 : ℂ → ℂ) = 1 := by
  change taylorSeries (fun _ : ℂ ↦ (1 : ℂ)) = 1
  ext k
  by_cases hk : k = 0 <;> simp [taylorSeries, iteratedDeriv_const, hk]

theorem taylorSeries_id : taylorSeries id = PowerSeries.X := by
  change taylorSeries (fun q : ℂ ↦ q) = PowerSeries.X
  ext k
  rcases k with _ | _ | k
  · simp [taylorSeries]
  · simp [taylorSeries, iteratedDeriv_fun_id_zero]
  · rw [coeff_taylorSeries, iteratedDeriv_fun_id_zero]
    simp [PowerSeries.coeff_X]

theorem taylorSeries_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (m : ℕ) :
    taylorSeries (f ^ m) = taylorSeries f ^ m := by
  induction m with
  | zero => simpa using taylorSeries_one
  | succ m ih =>
      rw [pow_succ, pow_succ, taylorSeries_mul (hf.pow m) hf, ih]

theorem taylorSeries_tprod_one_sub_pow :
    taylorSeries (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) := by
  ext k
  rw [coeff_taylorSeries]
  exact (coeff_tprod_one_sub_pow_eq_factorial_inv_mul_iteratedDeriv k).symm

theorem map_tprod_one_sub_X_pow :
    PowerSeries.map (Int.castRingHom ℂ)
        (∏' n : ℕ, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) := by
  ext k
  rw [PowerSeries.coeff_map,
    TateCurveRouteProbe.coeff_tprod_one_sub_X_pow_eq_prod_range ℤ k,
    TateCurveRouteProbe.coeff_tprod_one_sub_X_pow_eq_prod_range ℂ k]
  rw [← PowerSeries.coeff_map]
  congr 1
  simp

theorem analyticAt_tprod_one_sub_pow :
    AnalyticAt ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) 0 := by
  have hanalytic : AnalyticOnNhd ℂ
      (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) (Metric.ball 0 1) :=
    (analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
      ModularForm.differentiableOn_tprod_one_sub_pow
  exact hanalytic 0 (by simp)

theorem taylorSeries_deltaProduct :
    taylorSeries
        (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) =
      PowerSeries.X *
        (∏' n : ℕ,
          ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) ^ 24 := by
  change taylorSeries
      ((fun q : ℂ ↦ q) *
        (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) = _
  rw [taylorSeries_mul (by fun_prop) (analyticAt_tprod_one_sub_pow.pow 24)]
  change taylorSeries id * _ = _
  rw [taylorSeries_id,
    taylorSeries_pow analyticAt_tprod_one_sub_pow,
    taylorSeries_tprod_one_sub_pow]

theorem qExpansion_discriminant_eq_taylorSeries_deltaProduct :
    UpperHalfPlane.qExpansion 1 CuspForm.discriminant =
      taylorSeries
        (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) := by
  have hEq : Set.EqOn
      (UpperHalfPlane.cuspFunction 1 CuspForm.discriminant)
      (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24)
      (Metric.ball 0 1) := by
    intro q hq
    calc
      UpperHalfPlane.cuspFunction 1 CuspForm.discriminant q =
          q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
        simpa only [CuspForm.coe_discriminant] using
          ModularForm.discriminant_cuspFunction_eqOn hq
      _ = q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24 := by
        rw [(ModularForm.multipliable_one_sub_pow (by
          simpa [Metric.mem_ball, dist_zero_right] using hq)).tprod_pow 24]
  ext k
  rw [UpperHalfPlane.qExpansion_coeff, coeff_taylorSeries]
  congr 1
  exact hEq.iteratedDeriv_of_isOpen Metric.isOpen_ball k (by simp)

theorem formalProductQExpansionBridge :
    TateCurveRouteProbe.formalProductQExpansionBridge := by
  change PowerSeries.map (Int.castRingHom ℂ) TateCurve.ΔFormal =
    UpperHalfPlane.qExpansion 1 CuspForm.discriminant
  calc
    PowerSeries.map (Int.castRingHom ℂ) TateCurve.ΔFormal =
        PowerSeries.X *
          (∏' n : ℕ,
            ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1))) ^ 24 := by
      simp only [TateCurve.ΔFormal, map_mul, map_pow, PowerSeries.map_X]
      rw [map_tprod_one_sub_X_pow]
    _ = taylorSeries
        (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) :=
      taylorSeries_deltaProduct.symm
    _ = UpperHalfPlane.qExpansion 1 CuspForm.discriminant :=
      qExpansion_discriminant_eq_taylorSeries_deltaProduct.symm

theorem weierstrassDiscriminantFormal_eq_deltaFormal :
    TateCurve.weierstrassDiscriminantFormal = TateCurve.ΔFormal :=
  TateCurveRouteProbe.weierstrassDiscriminantFormal_eq_deltaFormal_of_bridge
    formalProductQExpansionBridge

#print axioms tendstoLocallyUniformlyOn_iteratedDeriv_partialProduct
#print axioms coeff_tprod_one_sub_pow_eq_factorial_inv_mul_iteratedDeriv
#print axioms map_tprod_one_sub_X_pow
#print axioms formalProductQExpansionBridge
#print axioms weierstrassDiscriminantFormal_eq_deltaFormal

end TateDeltaAnalyticBridgeProbe
