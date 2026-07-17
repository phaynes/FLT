/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.TorsionFiberCount
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

theorem prePsi_rootSet_card
    [IsSepClosed k] (E : WeierstrassCurve k) {n : ℕ}
    (hn : (n : k) ≠ 0) (hsep : (E.preΨ' n).Separable) :
    Fintype.card ((E.preΨ' n).rootSet k) =
      (n ^ 2 - if Even n then 4 else 1) / 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep
    (IsSepClosed.splits_domain (f := algebraMap k k) (E.preΨ' n) hsep)]
  exact E.natDegree_preΨ' hn

end

end FLTMethodology.Torsion
