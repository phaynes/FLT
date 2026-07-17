/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.KummerProjectivePropagation
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# All-characteristic nonvanishing and finite rational torsion

This module removes the characteristic restriction from the division-polynomial detector. After
base change to an algebraic closure, the monic positive-degree polynomial `Phi_n` has a root. The
proved nonzero Kummer representative then forces `PsiSq_n` to be a nonzero polynomial. Combined
with the all-index torsion detector, this gives finiteness of rational `n`-torsion for every
positive natural `n` over every field.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

theorem psiSq_ne_zero_all_characteristics
    (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : 0 < n) : E.ΨSq (n : ℤ) ≠ 0 := by
  intro hzero
  let K := AlgebraicClosure k
  let EK : WeierstrassCurve K := E.baseChange K
  letI : EK.IsElliptic := by
    change (E.map (algebraMap k K)).IsElliptic
    infer_instance
  have hPhiNe : EK.Φ (n : ℤ) ≠ 0 := EK.Φ_ne_zero (n : ℤ)
  have hPhiDegree : (EK.Φ (n : ℤ)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hPhiNe, EK.natDegree_Φ]
    simpa using hn.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EK.Φ (n : ℤ)) hPhiDegree
  have hrep := divisionPolynomialRep_ne_zero EK x n
  apply hrep
  funext i
  fin_cases i
  · simpa [divisionPolynomialRep] using hx
  · change (EK.ΨSq (n : ℤ)).eval x = 0
    rw [show EK.ΨSq (n : ℤ) = (E.ΨSq (n : ℤ)).map (algebraMap k K) by
      exact E.map_ΨSq (algebraMap k K) (n : ℤ)]
    rw [hzero, Polynomial.map_zero, Polynomial.eval_zero]

def psiSqTorsionXDetector_all_characteristics
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : 0 < n) : TorsionXDetector E n where
  polynomial := E.ΨSq (n : ℤ)
  polynomial_ne_zero := psiSq_ne_zero_all_characteristics E hn
  detects := psiSqDetectsNTorsion_nat E n

theorem n_torsion_finite_all_characteristics
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) :=
  n_torsion_finite_of_detector E (psiSqTorsionXDetector_all_characteristics E hn)

end

end FLTMethodology.Torsion
