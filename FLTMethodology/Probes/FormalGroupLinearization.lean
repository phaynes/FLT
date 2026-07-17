/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# First-order linearization of a formal group

This module proves the generic half of the multiplication-by-`n` differential needed at the
elliptic-torsion boundary. For an arbitrary one-dimensional formal group law, substitution into
two zero-constant one-variable series adds their linear coefficients. Consequently the linear
coefficient of the formal `n`-series is exactly `(n : R)`.

No elliptic-curve construction is used here. The remaining adapter must construct the elliptic
formal group and identify a `preΨ'` infinitesimal witness with a zero of its `n`-series.
-/

namespace FLTMethodology

open MvPowerSeries Finsupp

noncomputable section

variable {R : Type*} [CommRing R]

private lemma single_finTwo_zero_ne_one :
    (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
  intro h
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at h0

private lemma coeff_one_finTwo_prod (f g : PowerSeries R)
    (hf : f.constantCoeff = 0) (hg : g.constantCoeff = 0)
    (d : Fin 2 →₀ ℕ) :
    PowerSeries.coeff 1 (d.prod fun s e => (![f, g] s) ^ e) =
      if d = single 0 1 then PowerSeries.coeff 1 f
      else if d = single 1 1 then PowerSeries.coeff 1 g else 0 := by
  rw [Finsupp.prod_fintype d _ (by simp), Fin.prod_univ_two]
  simp only [PowerSeries.coeff_one_mul, map_pow,
    PowerSeries.coeff_one_pow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hf, hg]
  by_cases hd0 : d = single 0 1
  · subst d
    rw [if_pos rfl]
    simp
  by_cases hd1 : d = single 1 1
  · subst d
    rw [if_neg hd0, if_pos rfl]
    simp
  rw [if_neg hd0, if_neg hd1]
  generalize ha : d 0 = a
  generalize hb : d 1 = b
  cases a with
  | zero =>
      cases b with
      | zero => simp
      | succ b =>
          cases b with
          | zero =>
              exfalso
              apply hd1
              apply Finsupp.ext
              intro i
              fin_cases i <;> simp [ha, hb]
          | succ b => simp
  | succ a =>
      cases b with
      | zero =>
          cases a with
          | zero =>
              exfalso
              apply hd0
              apply Finsupp.ext
              intro i
              fin_cases i <;> simp [ha, hb]
          | succ a => simp
      | succ b => simp

/-- First-order addition in any one-dimensional formal group is ordinary addition. -/
theorem formalGroup_coeff_one_add (F : FormalGroup R) (f g : PowerSeries R)
    (hf : f.constantCoeff = 0) (hg : g.constantCoeff = 0) :
    PowerSeries.coeff 1 (F.toPowerSeries.subst ![f, g]) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> assumption)]
  rw [finsum_eq_sum_of_support_subset _ (s := {single 0 1, single 1 1})]
  · rw [Finset.sum_insert (by simpa using single_finTwo_zero_ne_one),
      Finset.sum_singleton]
    simp [F.lin_coeff_X, F.lin_coeff_Y]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    change d ∈ ({single 0 1, single 1 1} : Finset (Fin 2 →₀ ℕ))
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    push Not at hnot
    have hzero :
        MvPowerSeries.coeff (single () 1)
          (d.prod fun s e => (![f, g] s) ^ e) = 0 := by
      simpa [PowerSeries.coeff, hnot.1, hnot.2] using
        coeff_one_finTwo_prod f g hf hg d
    apply hd
    rw [hzero, smul_zero]

/-- The one-variable `n`-series associated to a formal group law. -/
def formalGroupNSeries (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => F.toPowerSeries.subst ![formalGroupNSeries F n, PowerSeries.X]

@[simp] theorem formalGroupNSeries_zero (F : FormalGroup R) :
    formalGroupNSeries F 0 = 0 := rfl

@[simp] theorem formalGroupNSeries_succ (F : FormalGroup R) (n : ℕ) :
    formalGroupNSeries F (n + 1) =
      F.toPowerSeries.subst ![formalGroupNSeries F n, PowerSeries.X] := rfl

/-- Every formal `n`-series has zero constant coefficient. -/
theorem formalGroupNSeries_constantCoeff (F : FormalGroup R) (n : ℕ) :
    (formalGroupNSeries F n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalGroupNSeries_succ]
      apply MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
          fin_cases i
          · exact ih
          · exact PowerSeries.constantCoeff_X)
        (fun i => by
          fin_cases i
          · exact ih
          · exact PowerSeries.constantCoeff_X)
        F.zero_constantCoeff

/-- The differential of multiplication by `n` in any one-dimensional formal group is scalar
multiplication by `(n : R)`. -/
theorem formalGroupNSeries_coeff_one (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (formalGroupNSeries F n) = (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalGroupNSeries_succ,
        formalGroup_coeff_one_add F _ _ (formalGroupNSeries_constantCoeff F n)
          PowerSeries.constantCoeff_X,
        ih, PowerSeries.coeff_one_X, Nat.cast_add, Nat.cast_one]

/-- If `(n : R)` is nonzero, the formal `n`-series is nonzero already at first order. -/
theorem formalGroupNSeries_ne_zero (F : FormalGroup R) {n : ℕ} (hn : (n : R) ≠ 0) :
    formalGroupNSeries F n ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (PowerSeries.coeff (R := R) 1) hzero
  rw [formalGroupNSeries_coeff_one, map_zero] at hcoeff
  exact hn hcoeff

end

end FLTMethodology
