/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.TorsionFiberCount
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed

/-!
# Parity decomposition for division-polynomial torsion counts

This module separates the remaining torsion-cardinality argument into its odd and even root sets.
It also turns separability of the quadratic curve fibre and of `prePsi'` into exact cardinalities.
The remaining mathematical boundary is therefore the required separability, even-case disjointness,
and the one-point fibre calculation over the two-torsion roots.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine BigOperators

noncomputable section

universe u

variable {k : Type u} [Field k]

theorem psiSq_rootSet_eq_prePsi_of_odd
    (E : WeierstrassCurve k) {n : ℕ} (hn : (n : k) ≠ 0) (hodd : Odd n) :
    (E.ΨSq (n : ℤ)).rootSet k = (E.preΨ' n).rootSet k := by
  have hpsi : E.ΨSq (n : ℤ) ≠ 0 := E.ΨSq_ne_zero (by exact_mod_cast hn)
  have hpre : E.preΨ' n ≠ 0 := E.preΨ'_ne_zero hn
  have hneven : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
  ext x
  rw [Polynomial.mem_rootSet_of_ne hpsi, Polynomial.mem_rootSet_of_ne hpre]
  rw [E.ΨSq_ofNat, if_neg hneven]
  simp

theorem psiSq_rootSet_eq_prePsi_union_psiTwo_of_even
    (E : WeierstrassCurve k) {n : ℕ} (hn : (n : k) ≠ 0) (heven : Even n) :
    (E.ΨSq (n : ℤ)).rootSet k =
      (E.preΨ' n).rootSet k ∪ E.Ψ₂Sq.rootSet k := by
  have hpsi : E.ΨSq (n : ℤ) ≠ 0 := E.ΨSq_ne_zero (by exact_mod_cast hn)
  have hpre : E.preΨ' n ≠ 0 := E.preΨ'_ne_zero hn
  have htwo : E.Ψ₂Sq ≠ 0 := by
    intro hzero
    apply hpsi
    rw [E.ΨSq_ofNat, if_pos heven, hzero, mul_zero]
  ext x
  rw [Polynomial.mem_rootSet_of_ne hpsi]
  change _ ↔ x ∈ (E.preΨ' n).rootSet k ∨ x ∈ E.Ψ₂Sq.rootSet k
  rw [Polynomial.mem_rootSet_of_ne hpre, Polynomial.mem_rootSet_of_ne htwo]
  rw [E.ΨSq_ofNat, if_pos heven]
  simp

theorem curveYFiber_card_eq_two_of_separable
    [IsSepClosed k] (E : WeierstrassCurve k) (x : k)
    (hsep : (fiberPolynomial E x).Separable) :
    Nat.card (curveYFiber E x) = 2 := by
  rw [Nat.card_congr (show curveYFiber E x ≃ (fiberPolynomial E x).rootSet k from by
    exact Equiv.subtypeEquiv (Equiv.refl k) <| by
      intro y
      simp only [curveYFiber, Set.mem_setOf_eq, Equiv.refl_apply]
      rw [equation_iff_eval_fiberPolynomial]
      exact (Polynomial.mem_rootSet_of_ne (fiberPolynomial_ne_zero E x)).symm)]
  rw [Nat.card_eq_fintype_card]
  rw [Polynomial.card_rootSet_eq_natDegree hsep
    (IsSepClosed.splits_domain (f := algebraMap k k) (fiberPolynomial E x) hsep)]
  exact (isMonicOfDegree_add_add_two
    (E.a₁ * x + E.a₃)
    (-(x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆))).natDegree_eq

theorem psiTwoSq_separable
    (E : WeierstrassCurve k) [E.IsElliptic] (h2 : (2 : k) ≠ 0) :
    E.Ψ₂Sq.Separable := by
  let P : Cubic k := E.twoTorsionPolynomial
  let K := AlgebraicClosure k
  let f : k →+* K := algebraMap k K
  have ha : P.a ≠ 0 := by
    dsimp [P, WeierstrassCurve.twoTorsionPolynomial]
    rw [show (4 : k) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have hP : P.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have hsplits : (P.toPoly.map f).Splits := IsAlgClosed.splits _
  have hdiscr : P.discr ≠ 0 := by
    exact E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic
      (isUnit_iff_ne_zero.mpr h2)
  have hnodup : (P.toPoly.aroots K).Nodup := by
    rw [Polynomial.aroots_def]
    rw [← Cubic.map_roots]
    exact (Cubic.discr_ne_zero_iff_roots_nodup ha hsplits).mp hdiscr
  have hsepP : P.toPoly.Separable :=
    (Polynomial.nodup_aroots_iff_of_splits hP hsplits).mp hnodup
  simpa [P, WeierstrassCurve.Ψ₂Sq_eq] using hsepP

theorem psiTwoSq_rootSet_card
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic] (h2 : (2 : k) ≠ 0) :
    Fintype.card (E.Ψ₂Sq.rootSet k) = 3 := by
  have hsep := psiTwoSq_separable E h2
  rw [Polynomial.card_rootSet_eq_natDegree hsep
    (IsSepClosed.splits_domain (f := algebraMap k k) E.Ψ₂Sq hsep)]
  apply E.natDegree_Ψ₂Sq
  rw [show (4 : k) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 h2

theorem psiTwoSq_eval_eq_fiber_discriminant
    (E : WeierstrassCurve k) (x : k) :
    E.Ψ₂Sq.eval x =
      (E.a₁ * x + E.a₃) ^ 2 +
        4 * (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero
    (E : WeierstrassCurve k) (x : k) (hd : E.Ψ₂Sq.eval x ≠ 0) :
    (fiberPolynomial E x).Separable := by
  let f : k[X] := fiberPolynomial E x
  let d : k := E.Ψ₂Sq.eval x
  let b : k := E.a₁ * x + E.a₃
  let c : k := x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆
  have hd' : d ≠ 0 := hd
  have hdisc : d = b ^ 2 + 4 * c := psiTwoSq_eval_eq_fiber_discriminant E x
  have hfiber : derivative f ^ 2 - 4 * f = C d := by
    change derivative (X ^ 2 + C b * X + C (-c)) ^ 2 -
      4 * (X ^ 2 + C b * X + C (-c)) = C d
    simp only [derivative_add, derivative_pow, derivative_X,
      derivative_mul, derivative_neg, derivative_C, Nat.cast_ofNat, zero_mul, zero_add,
      mul_one, Polynomial.C_ofNat, Polynomial.C_neg]
    have hdiscC : C d = C b ^ 2 + 4 * C c := by
      rw [hdisc, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
        Polynomial.C_ofNat]
    linear_combination -hdiscC
  have hinv : C (1 / d) * C d = (1 : k[X]) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_1]
    congr 1
    field_simp [hd']
  have hneg : C (-4 / d) = (-4 : k[X]) * C (1 / d) := by
    calc
      C (-4 / d) = C ((-4) * (1 / d)) := by
        congr 1
        field_simp [hd']
      _ = C (-4) * C (1 / d) := by rw [Polynomial.C_mul]
      _ = (-4 : k[X]) * C (1 / d) := by
        rw [Polynomial.C_neg, Polynomial.C_ofNat]
  rw [Polynomial.separable_def']
  refine ⟨C (-4 / d), C (1 / d) * derivative f, ?_⟩
  rw [hneg]
  calc
    (-4 : k[X]) * C (1 / d) * f +
        (C (1 / d) * derivative f) * derivative f =
        C (1 / d) * (derivative f ^ 2 - 4 * f) := by ring
    _ = C (1 / d) * C d := by rw [hfiber]
    _ = 1 := hinv

theorem curveYFiber_card_eq_one_of_psiTwoSq_root
    (E : WeierstrassCurve k) (x : k) (h2 : (2 : k) ≠ 0)
    (hroot : E.Ψ₂Sq.eval x = 0) :
    Nat.card (curveYFiber E x) = 1 := by
  let b : k := E.a₁ * x + E.a₃
  let c : k := x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆
  have hdisc : b ^ 2 + 4 * c = 0 := by
    rw [← psiTwoSq_eval_eq_fiber_discriminant E x]
    exact hroot
  have hmem : E.toAffine.Equation x (-b / 2) := by
    rw [equation_iff_eval_fiberPolynomial]
    simp only [fiberPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    dsimp [b, c] at hdisc ⊢
    field_simp [h2]
    ring_nf at hdisc ⊢
    linear_combination -hdisc
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro y z
    apply Subtype.ext
    have hy := y.2
    have hz := z.2
    change E.toAffine.Equation x y.1 at hy
    change E.toAffine.Equation x z.1 at hz
    rw [equation_iff_eval_fiberPolynomial] at hy hz
    simp only [fiberPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hy hz
    have hylinear : 2 * y.1 + b = 0 := by
      apply sq_eq_zero_iff.mp
      linear_combination 4 * hy + hdisc
    have hzlinear : 2 * z.1 + b = 0 := by
      apply sq_eq_zero_iff.mp
      linear_combination 4 * hz + hdisc
    apply (mul_left_cancel₀ h2)
    linear_combination hylinear - hzlinear
  · exact ⟨⟨-b / 2, hmem⟩⟩

theorem prePsi_rootSet_card
    [IsSepClosed k] (E : WeierstrassCurve k) {n : ℕ}
    (hn : (n : k) ≠ 0) (hsep : (E.preΨ' n).Separable) :
    Fintype.card ((E.preΨ' n).rootSet k) =
      (n ^ 2 - if Even n then 4 else 1) / 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep
    (IsSepClosed.splits_domain (f := algebraMap k k) (E.preΨ' n) hsep)]
  exact E.natDegree_preΨ' hn

theorem sum_set_union_of_disjoint
    {k : Type*} (s t : Set k) [Fintype s] [Fintype t]
    [Fintype (s ∪ t : Set k)] (f : k → ℕ) (h : Disjoint s t) :
    (∑ x : (s ∪ t : Set k), f x) = (∑ x : s, f x) + ∑ x : t, f x := by
  classical
  rw [Fintype.sum_equiv (Equiv.Set.union h)
    (fun x : (s ∪ t : Set k) ↦ f x)
    (fun x : s ⊕ t ↦ Sum.elim (fun y : s ↦ f y) (fun y : t ↦ f y) x)
    (by
      intro x
      by_cases hx : (x : k) ∈ s
      · rw [Equiv.Set.union_apply_left h hx]
        rfl
      · have hxt : (x : k) ∈ t := x.2.resolve_left hx
        rw [Equiv.Set.union_apply_right h hxt]
        rfl)]
  exact Fintype.sum_sum_type _

theorem sum_set_eq_of_eq
    {k : Type*} {s t : Set k} [Fintype s] [Fintype t]
    (f : k → ℕ) (h : s = t) :
    (∑ x : s, f x) = ∑ x : t, f x := by
  classical
  exact Fintype.sum_equiv (Equiv.setCongr h)
    (fun x : s ↦ f x) (fun x : t ↦ f x) (by intro x; rfl)

/-- The characteristic-safe assembly boundary for the exact affine torsion count. -/
theorem psiSqAffineZeroCard_of_prePsi_separable_coprime
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    (hpresep : (E.preΨ' n).Separable)
    (hcoprime : ∀ x : k, (E.preΨ' n).eval x = 0 → E.Ψ₂Sq.eval x ≠ 0) :
    PsiSqAffineZeroCard E n := by
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    exact hn (Nat.cast_zero)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  unfold PsiSqAffineZeroCard
  rw [psiSqAffineZeroCard_eq_sum_yFibers E hnpos]
  rcases n.even_or_odd with heven | hodd
  · have h2 : (2 : k) ≠ 0 := by
      intro hzero
      rcases heven with ⟨m, hm⟩
      apply hn
      rw [hm, Nat.cast_add]
      calc
        (m : k) + (m : k) = (2 : k) * (m : k) := by ring
        _ = 0 := by rw [hzero, zero_mul]
    have hpsiTwoSep := psiTwoSq_separable E h2
    have hpsiTwo : E.Ψ₂Sq ≠ 0 := hpsiTwoSep.ne_zero
    have hdisj : Disjoint ((E.preΨ' n).rootSet k) (E.Ψ₂Sq.rootSet k) := by
      rw [Set.disjoint_left]
      intro x hxpre hxpsi
      have hxprezero : (E.preΨ' n).eval x = 0 := by
        simpa using (Polynomial.mem_rootSet_of_ne hpresep.ne_zero).1 hxpre
      have hxpsizero : E.Ψ₂Sq.eval x = 0 := by
        simpa using (Polynomial.mem_rootSet_of_ne hpsiTwo).1 hxpsi
      exact (hcoprime x hxprezero) hxpsizero
    letI : Fintype ((E.preΨ' n).rootSet k ∪ E.Ψ₂Sq.rootSet k : Set k) :=
      ((Polynomial.rootSet_finite (E.preΨ' n) k).union
        (Polynomial.rootSet_finite E.Ψ₂Sq k)).fintype
    rw [sum_set_eq_of_eq (fun x : k ↦ Nat.card (curveYFiber E x))
      (psiSq_rootSet_eq_prePsi_union_psiTwo_of_even E hn heven)]
    rw [sum_set_union_of_disjoint ((E.preΨ' n).rootSet k) (E.Ψ₂Sq.rootSet k)
      (fun x : k ↦ Nat.card (curveYFiber E x)) hdisj]
    have hpreSum :
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
          Fintype.card ((E.preΨ' n).rootSet k) * 2 := by
      calc
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : (E.preΨ' n).rootSet k, 2 := by
              apply Fintype.sum_congr
              intro x
              have hxprezero : (E.preΨ' n).eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpresep.ne_zero).1 x.2
              have hxeval : E.Ψ₂Sq.eval (x : k) ≠ 0 := hcoprime (x : k) hxprezero
              exact curveYFiber_card_eq_two_of_separable E (x : k)
                (fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero E (x : k) hxeval)
        _ = Fintype.card ((E.preΨ' n).rootSet k) * 2 := by simp
    have htwoSum :
        (∑ x : E.Ψ₂Sq.rootSet k, Nat.card (curveYFiber E x)) =
          Fintype.card (E.Ψ₂Sq.rootSet k) := by
      calc
        (∑ x : E.Ψ₂Sq.rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : E.Ψ₂Sq.rootSet k, 1 := by
              apply Fintype.sum_congr
              intro x
              have hxzero : E.Ψ₂Sq.eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpsiTwo).1 x.2
              exact curveYFiber_card_eq_one_of_psiTwoSq_root E (x : k) h2 hxzero
        _ = Fintype.card (E.Ψ₂Sq.rootSet k) := by simp
    rw [hpreSum, htwoSum]
    rw [prePsi_rootSet_card E hn hpresep, if_pos heven]
    rw [psiTwoSq_rootSet_card E h2]
    have hfour : 4 ≤ n ^ 2 := by
      have heven' := heven
      rcases heven' with ⟨m, hm⟩
      have hn2 : 2 ≤ n := by omega
      nlinarith
    have hdiv : 2 ∣ n ^ 2 - 4 := by
      apply Nat.dvd_sub
      · rw [pow_two]
        exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp heven) n
      · norm_num
    rw [Nat.div_mul_cancel hdiv]
    omega
  · rw [sum_set_eq_of_eq (fun x : k ↦ Nat.card (curveYFiber E x))
      (psiSq_rootSet_eq_prePsi_of_odd E hn hodd)]
    have hpreSum :
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
          Fintype.card ((E.preΨ' n).rootSet k) * 2 := by
      calc
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : (E.preΨ' n).rootSet k, 2 := by
              apply Fintype.sum_congr
              intro x
              have hxprezero : (E.preΨ' n).eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpresep.ne_zero).1 x.2
              have hxeval : E.Ψ₂Sq.eval (x : k) ≠ 0 := hcoprime (x : k) hxprezero
              exact curveYFiber_card_eq_two_of_separable E (x : k)
                (fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero E (x : k) hxeval)
        _ = Fintype.card ((E.preΨ' n).rootSet k) * 2 := by simp
    rw [hpreSum]
    rw [prePsi_rootSet_card E hn hpresep]
    rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]
    have hdiv : 2 ∣ n ^ 2 - 1 := by
      have hoddsq : Odd (n ^ 2) := by
        simpa only [pow_two] using Odd.mul hodd hodd
      rcases hoddsq with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [hm]
      omega
    exact Nat.div_mul_cancel hdiv

end

end FLTMethodology.Torsion
