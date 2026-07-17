/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.PrePsiTwoTorsion

/-!
# Recovering division-polynomial separability from the exact torsion count

The forward counting argument proves `#E[n] = n²` once `preΨ' n` is separable.  This file proves
the converse.  Exact torsion cardinality fixes the cardinality of the affine `ΨSq` zero locus.
The already-proved pointwise coprimality with `Ψ₂Sq` then makes every `preΨ'` root contribute
exactly two affine points; in the even case the three two-torsion roots contribute one point each.
Consequently `preΨ' n` has as many distinct roots as its degree, hence is separable over a
separably closed field.

This converse permits an algebraically closed torsion-cardinality provider to discharge the local
separability boundary without constructing a second formal-group implementation.
-/

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine BigOperators

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- Exact torsion cardinality forces `preΨ' n` to be separable. -/
theorem prePsi_separable_of_n_torsion_card
    [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0)
    (hcard : Nat.card (E.nTorsion n) = n ^ 2) :
    (E.preΨ' n).Separable := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn Nat.cast_zero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hpre : E.preΨ' n ≠ 0 := E.preΨ'_ne_zero hn
  have hcoprime := prePsi_pointwise_coprime E hn
  have hzeroCard : Nat.card (psiSqAffineZeroSet E n) = n ^ 2 - 1 := by
    have hfinite : (psiSqAffineZeroSet E n).Finite := by
      simpa only [psiSqAffineZeroSet, detectedAffineSet] using
        detectedAffineSet_finite E (E.ΨSq (n : ℤ))
          (psiSq_ne_zero_all_characteristics E hnpos)
    letI : Finite (psiSqAffineZeroSet E n) := hfinite
    have h := Nat.card_congr (nTorsionEquivWithZeroPsiSqZero E n)
    change Nat.card (E.nTorsion n) = Nat.card (Option (psiSqAffineZeroSet E n)) at h
    rw [Finite.card_option] at h
    omega
  have hsum :
      (∑ x : (E.ΨSq (n : ℤ)).rootSet k, Nat.card (curveYFiber E x)) = n ^ 2 - 1 := by
    rw [← psiSqAffineZeroCard_eq_sum_yFibers E hnpos]
    exact hzeroCard
  apply (Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := k) hpre
    (IsAlgClosed.splits_domain (E.preΨ' n))).mp
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
        simpa using (Polynomial.mem_rootSet_of_ne hpre).1 hxpre
      have hxpsizero : E.Ψ₂Sq.eval x = 0 := by
        simpa using (Polynomial.mem_rootSet_of_ne hpsiTwo).1 hxpsi
      exact (hcoprime x hxprezero) hxpsizero
    letI : Fintype ((E.preΨ' n).rootSet k ∪ E.Ψ₂Sq.rootSet k : Set k) :=
      ((Polynomial.rootSet_finite (E.preΨ' n) k).union
        (Polynomial.rootSet_finite E.Ψ₂Sq k)).fintype
    rw [sum_set_eq_of_eq (fun x : k ↦ Nat.card (curveYFiber E x))
      (psiSq_rootSet_eq_prePsi_union_psiTwo_of_even E hn heven)] at hsum
    rw [sum_set_union_of_disjoint ((E.preΨ' n).rootSet k) (E.Ψ₂Sq.rootSet k)
      (fun x : k ↦ Nat.card (curveYFiber E x)) hdisj] at hsum
    have hpreSum :
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
          Fintype.card ((E.preΨ' n).rootSet k) * 2 := by
      calc
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : (E.preΨ' n).rootSet k, 2 := by
              apply Fintype.sum_congr
              intro x
              have hxprezero : (E.preΨ' n).eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpre).1 x.2
              exact curveYFiber_card_eq_two_of_separable E (x : k)
                (fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero E (x : k)
                  (hcoprime (x : k) hxprezero))
        _ = Fintype.card ((E.preΨ' n).rootSet k) * 2 := by simp
    have htwoSum :
        (∑ x : E.Ψ₂Sq.rootSet k, Nat.card (curveYFiber E x)) = 3 := by
      calc
        (∑ x : E.Ψ₂Sq.rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : E.Ψ₂Sq.rootSet k, 1 := by
              apply Fintype.sum_congr
              intro x
              have hxzero : E.Ψ₂Sq.eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpsiTwo).1 x.2
              exact curveYFiber_card_eq_one_of_psiTwoSq_root E (x : k) h2 hxzero
        _ = Fintype.card (E.Ψ₂Sq.rootSet k) := by simp
        _ = 3 := psiTwoSq_rootSet_card E h2
    rw [hpreSum, htwoSum] at hsum
    rw [E.natDegree_preΨ' hn, if_pos heven]
    rcases heven with ⟨m, hm⟩
    omega
  · rw [sum_set_eq_of_eq (fun x : k ↦ Nat.card (curveYFiber E x))
      (psiSq_rootSet_eq_prePsi_of_odd E hn hodd)] at hsum
    have hpreSum :
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
          Fintype.card ((E.preΨ' n).rootSet k) * 2 := by
      calc
        (∑ x : (E.preΨ' n).rootSet k, Nat.card (curveYFiber E x)) =
            ∑ _x : (E.preΨ' n).rootSet k, 2 := by
              apply Fintype.sum_congr
              intro x
              have hxprezero : (E.preΨ' n).eval (x : k) = 0 := by
                simpa using (Polynomial.mem_rootSet_of_ne hpre).1 x.2
              exact curveYFiber_card_eq_two_of_separable E (x : k)
                (fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero E (x : k)
                  (hcoprime (x : k) hxprezero))
        _ = Fintype.card ((E.preΨ' n).rootSet k) * 2 := by simp
    rw [hpreSum] at hsum
    rw [E.natDegree_preΨ' hn, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    rcases hodd with ⟨m, hm⟩
    omega

#print axioms prePsi_separable_of_n_torsion_card

end

end FLTMethodology.Torsion
