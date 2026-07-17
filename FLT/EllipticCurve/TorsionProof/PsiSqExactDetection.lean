/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.PsiSqAllCharacteristic

/-!
# Exact division-polynomial detection of affine torsion

The all-index Kummer relation initially gives the implication from torsion to a `PsiSq_n` root.
Nonvanishing of the companion `Phi_n` coordinate upgrades this to an equivalence: an affine point
is killed by `n` exactly when its x-coordinate is a root of `PsiSq_n`. This isolates the remaining
separably-closed cardinality problem as a root-multiplicity and y-fibre count.
-/

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

theorem phi_eval_ne_zero_of_psiSq_eval_eq_zero
    (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} {x : k} (hpsi : (E.ΨSq (n : ℤ)).eval x = 0) :
    (E.Φ (n : ℤ)).eval x ≠ 0 := by
  intro hphi
  apply divisionPolynomialRep_ne_zero E x n
  funext i
  fin_cases i
  · exact hphi
  · exact hpsi

theorem psiSq_eval_eq_zero_iff_nsmul_eq_zero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} {x y : k} (h : E.toAffine.Nonsingular x y) :
    (E.ΨSq (n : ℤ)).eval x = 0 ↔
      (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0 := by
  let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x y h
  let Q : (E⁄k).Point := (n : ℤ) • P
  constructor
  · intro hpsi
    have hphi : (E.Φ (n : ℤ)).eval x ≠ 0 :=
      phi_eval_ne_zero_of_psiSq_eval_eq_zero E hpsi
    have hhom := divisionPolynomialXHomogeneous_nat E n h
    change Q.xRep 0 * (E.ΨSq (n : ℤ)).eval x =
      Q.xRep 1 * (E.Φ (n : ℤ)).eval x at hhom
    have hz : Q.xRep 1 = 0 := by
      have hmul : Q.xRep 1 * (E.Φ (n : ℤ)).eval x = 0 := by
        rw [hpsi, mul_zero] at hhom
        exact hhom.symm
      exact (mul_eq_zero.mp hmul).resolve_right hphi
    change Q = 0
    generalize hQeq : Q = R at hz ⊢
    cases R with
    | zero => rfl
    | some xQ yQ hQ =>
        simp [WeierstrassCurve.Affine.Point.xRep] at hz
  · intro htorsion
    exact psiSqDetectsNTorsion_nat E n h htorsion

end

end FLTMethodology.Torsion
