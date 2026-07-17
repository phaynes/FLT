/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.TorsionParityCount

/-!
# Division-polynomial values at two-torsion coordinates

This module isolates the algebra needed to prove that `preΨ' n` does not vanish at a root of
`Ψ₂Sq`. In characteristic different from two, it proves the relations between the first two
nontrivial elliptic-divisibility terms and reduces every later evaluation to `preNormEDS'` with
zero first parameter. The remaining step is the closed nonvanishing formula for that specialized
recurrence.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve

noncomputable section

universe u

variable {k : Type u} [Field k]

theorem prePsiFour_eval_sq_eq_neg_four_psiThree_cube
    (E : WeierstrassCurve k) (x : k) (h2 : (2 : k) ≠ 0)
    (hq : E.Ψ₂Sq.eval x = 0) :
    E.preΨ₄.eval x ^ 2 = -4 * E.Ψ₃.eval x ^ 3 := by
  have hb := b_two_mul_b_six_sub_b_four_sq E
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hb₆ : E.b₆ = -(4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x) := by
    simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    linear_combination hq
  have hb₈ : E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
    apply (eq_div_iff h4).2
    linear_combination -hb
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat]
  rw [hb₆] at hb₈ ⊢
  rw [hb₈]
  field_simp [h4]
  ring

theorem psiTwoSq_derivative_eval_sq_eq_neg_sixteen_psiThree
    (E : WeierstrassCurve k) (x : k) (h2 : (2 : k) ≠ 0)
    (hq : E.Ψ₂Sq.eval x = 0) :
    E.Ψ₂Sq.derivative.eval x ^ 2 = -16 * E.Ψ₃.eval x := by
  have hb := b_two_mul_b_six_sub_b_four_sq E
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hb₆ : E.b₆ = -(4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x) := by
    simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    linear_combination hq
  have hb₈ : E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
    apply (eq_div_iff h4).2
    linear_combination -hb
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_zero, zero_mul, zero_add, mul_one]
  rw [hb₆] at hb₈ ⊢
  rw [hb₈]
  field_simp [h4]
  ring

theorem psiThree_eval_ne_zero_of_psiTwoSq_root
    (E : WeierstrassCurve k) [E.IsElliptic] (x : k) (h2 : (2 : k) ≠ 0)
    (hq : E.Ψ₂Sq.eval x = 0) :
    E.Ψ₃.eval x ≠ 0 := by
  have hderiv : E.Ψ₂Sq.derivative.eval x ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using
      (psiTwoSq_separable E h2).eval₂_derivative_ne_zero (RingHom.id k) hq
  intro hc
  apply hderiv
  apply sq_eq_zero_iff.mp
  rw [psiTwoSq_derivative_eval_sq_eq_neg_sixteen_psiThree E x h2 hq, hc, mul_zero]

theorem prePsiFour_eval_ne_zero_of_psiTwoSq_root
    (E : WeierstrassCurve k) [E.IsElliptic] (x : k) (h2 : (2 : k) ≠ 0)
    (hq : E.Ψ₂Sq.eval x = 0) :
    E.preΨ₄.eval x ≠ 0 := by
  have hc := psiThree_eval_ne_zero_of_psiTwoSq_root E x h2 hq
  intro hd
  have hrel := prePsiFour_eval_sq_eq_neg_four_psiThree_cube E x h2 hq
  rw [hd, zero_pow (by norm_num)] at hrel
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hc3 : E.Ψ₃.eval x ^ 3 = 0 :=
    (mul_eq_zero.mp hrel.symm).resolve_left (neg_ne_zero.mpr h4)
  exact (pow_ne_zero 3 hc) hc3

theorem prePsi_eval_eq_preNormEDS_at_psiTwoSq_root
    (E : WeierstrassCurve k) (x : k) (n : ℕ)
    (hq : E.Ψ₂Sq.eval x = 0) :
    (E.preΨ' n).eval x =
      preNormEDS' 0 (E.Ψ₃.eval x) (E.preΨ₄.eval x) n := by
  change (Polynomial.evalRingHom x)
      (preNormEDS' (E.Ψ₂Sq ^ 2) E.Ψ₃ E.preΨ₄ n) = _
  rw [map_preNormEDS']
  rw [map_pow]
  change preNormEDS' (E.Ψ₂Sq.eval x ^ 2) (E.Ψ₃.eval x) (E.preΨ₄.eval x) n = _
  rw [hq, zero_pow (by norm_num)]

end

end FLTMethodology.Torsion
