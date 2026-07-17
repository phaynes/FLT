/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.SpecialPreNormEDS

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
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

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

theorem prePsi_eval_ne_zero_of_odd_at_psiTwoSq_root
    (E : WeierstrassCurve k) [E.IsElliptic] {n : ℕ} (hodd : Odd n)
    (x : k) (hq : E.Ψ₂Sq.eval x = 0) :
    (E.preΨ' n).eval x ≠ 0 := by
  intro hpre
  let K := AlgebraicClosure k
  letI : DecidableEq K := Classical.decEq K
  let EK : WeierstrassCurve K := E.baseChange K
  letI : EK.IsElliptic := by
    change (E.map (algebraMap k K)).IsElliptic
    infer_instance
  let xK : K := algebraMap k K x
  have hpreK : (EK.preΨ' n).eval xK = 0 := by
    rw [show EK.preΨ' n = (E.preΨ' n).map (algebraMap k K) by
      exact E.map_preΨ' (algebraMap k K) n]
    dsimp only [xK]
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hpre, map_zero]
  have hqK : EK.Ψ₂Sq.eval xK = 0 := by
    rw [show EK.Ψ₂Sq = E.Ψ₂Sq.map (algebraMap k K) by
      exact E.map_Ψ₂Sq (algebraMap k K)]
    dsimp only [xK]
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hq, map_zero]
  have hfiberNe : fiberPolynomial EK xK ≠ 0 := fiberPolynomial_ne_zero EK xK
  have hfiberNatDegree : (fiberPolynomial EK xK).natDegree = 2 :=
    (isMonicOfDegree_add_add_two
      (EK.a₁ * xK + EK.a₃)
      (-(xK ^ 3 + EK.a₂ * xK ^ 2 + EK.a₄ * xK + EK.a₆))).natDegree_eq
  have hfiberDegree : (fiberPolynomial EK xK).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hfiberNe, hfiberNatDegree]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (fiberPolynomial EK xK) hfiberDegree
  have heq : EK.toAffine.Equation xK y :=
    (equation_iff_eval_fiberPolynomial EK xK y).2 hy
  have hns : EK.toAffine.Nonsingular xK y :=
    EK.toAffine.equation_iff_nonsingular.mp heq
  let P : (EK⁄K).Point := WeierstrassCurve.Affine.Point.some xK y hns
  have hpsiN : (EK.ΨSq (n : ℤ)).eval xK = 0 := by
    rw [EK.ΨSq_ofNat, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    norm_num [hpreK]
  have hpsiTwo : (EK.ΨSq (2 : ℤ)).eval xK = 0 := by
    rw [EK.ΨSq_two]
    exact hqK
  have hnP : (n : ℤ) • P = 0 :=
    (psiSq_eval_eq_zero_iff_nsmul_eq_zero EK hns).1 hpsiN
  have htwoP : (2 : ℤ) • P = 0 :=
    (psiSq_eval_eq_zero_iff_nsmul_eq_zero EK hns).1 hpsiTwo
  have hcoprime : IsCoprime (n : ℤ) (2 : ℤ) :=
    (Nat.coprime_two_right.mpr hodd).isCoprime
  rcases hcoprime with ⟨a, b, hab⟩
  have hPzero : P = 0 := by
    calc
      P = (1 : ℤ) • P := by simp
      _ = (a * (n : ℤ) + b * 2) • P := by rw [hab]
      _ = a • ((n : ℤ) • P) + b • ((2 : ℤ) • P) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hnP, htwoP, zsmul_zero, zsmul_zero, add_zero]
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns hPzero

theorem prePsi_pointwise_coprime_of_even_preNormEDS
    (E : WeierstrassCurve k) [E.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0)
    (hEven : ∀ {c d : k} {m : ℕ}, Even m → (m : k) ≠ 0 → c ≠ 0 →
      d ^ 2 = -4 * c ^ 3 → preNormEDS' 0 c d m ≠ 0) :
    ∀ x : k, (E.preΨ' n).eval x = 0 → E.Ψ₂Sq.eval x ≠ 0 := by
  intro x hpre hq
  rcases n.even_or_odd with heven | hodd
  · have h2 : (2 : k) ≠ 0 := by
      intro hzero
      rcases heven with ⟨m, hm⟩
      apply hn
      rw [hm, Nat.cast_add]
      calc
        (m : k) + (m : k) = (2 : k) * (m : k) := by ring
        _ = 0 := by rw [hzero, zero_mul]
    have hc : E.Ψ₃.eval x ≠ 0 :=
      psiThree_eval_ne_zero_of_psiTwoSq_root E x h2 hq
    have hrel : E.preΨ₄.eval x ^ 2 = -4 * E.Ψ₃.eval x ^ 3 :=
      prePsiFour_eval_sq_eq_neg_four_psiThree_cube E x h2 hq
    have hspecial :
        preNormEDS' 0 (E.Ψ₃.eval x) (E.preΨ₄.eval x) n ≠ 0 :=
      hEven heven hn hc hrel
    apply hspecial
    rw [← prePsi_eval_eq_preNormEDS_at_psiTwoSq_root E x n hq]
    exact hpre
  · exact (prePsi_eval_ne_zero_of_odd_at_psiTwoSq_root E hodd x hq) hpre

theorem psiSqAffineZeroCard_of_prePsi_separable_evenPreNormEDS
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) (hpresep : (E.preΨ' n).Separable)
    (hEven : ∀ {c d : k} {m : ℕ}, Even m → (m : k) ≠ 0 → c ≠ 0 →
      d ^ 2 = -4 * c ^ 3 → preNormEDS' 0 c d m ≠ 0) :
    PsiSqAffineZeroCard E n :=
  psiSqAffineZeroCard_of_prePsi_separable_coprime E hn hpresep
    (prePsi_pointwise_coprime_of_even_preNormEDS E hn hEven)

theorem n_torsion_card_of_prePsi_separable_evenPreNormEDS
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0) (hpresep : (E.preΨ' n).Separable)
    (hEven : ∀ {c d : k} {m : ℕ}, Even m → (m : k) ≠ 0 → c ≠ 0 →
      d ^ 2 = -4 * c ^ 3 → preNormEDS' 0 c d m ≠ 0) :
    Nat.card (E.nTorsion n) = n ^ 2 := by
  apply n_torsion_card_of_psiSq_affine_zero_card E
  · exact Nat.pos_of_ne_zero (fun hnzero ↦ hn (hnzero ▸ Nat.cast_zero))
  · exact psiSqAffineZeroCard_of_prePsi_separable_evenPreNormEDS E hn hpresep hEven

/-- The division-polynomial factor `preΨ' n` is pointwise coprime to `Ψ₂Sq` whenever `n` remains
nonzero in the coefficient field. -/
theorem prePsi_pointwise_coprime
    (E : WeierstrassCurve k) [E.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) :
    ∀ x : k, (E.preΨ' n).eval x = 0 → E.Ψ₂Sq.eval x ≠ 0 :=
  prePsi_pointwise_coprime_of_even_preNormEDS E hn fun hm hmk hc hrel ↦
    specialEvenPreNormEDS_ne_zero hm hmk hc hrel

/-- Exact affine torsion-coordinate count, conditional only on separability of `preΨ' n`. -/
theorem psiSqAffineZeroCard_of_prePsi_separable
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) (hpresep : (E.preΨ' n).Separable) :
    PsiSqAffineZeroCard E n :=
  psiSqAffineZeroCard_of_prePsi_separable_coprime E hn hpresep
    (prePsi_pointwise_coprime E hn)

/-- Exact `n`-torsion cardinality, conditional only on separability of `preΨ' n`. -/
theorem n_torsion_card_of_prePsi_separable
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0) (hpresep : (E.preΨ' n).Separable) :
    Nat.card (E.nTorsion n) = n ^ 2 := by
  apply n_torsion_card_of_psiSq_affine_zero_card E
  · exact Nat.pos_of_ne_zero (fun hnzero ↦ hn (hnzero ▸ Nat.cast_zero))
  · exact psiSqAffineZeroCard_of_prePsi_separable E hn hpresep

end

end FLTMethodology.Torsion
