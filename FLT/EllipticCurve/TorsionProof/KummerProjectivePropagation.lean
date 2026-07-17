/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.KummerAddSubPoint

/-!
# Projective propagation for the division-polynomial Kummer ladder

This module combines the unconditional synchronized division-polynomial ladder with the all-point
`addSubMap` theorem. It proves that the evaluated pair `![Φₙ(x), ΨSqₙ(x)]` is never the zero vector,
propagates its projective equality with the Kummer coordinate of `n • P`, and exports the
denominator-free x-coordinate relation and torsion detector for every natural index.
-/

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

def symmetricPair2 (u v : Fin 2 → k) : Fin 3 → k :=
  ![u 0 * v 0, u 0 * v 1 + u 1 * v 0, u 1 * v 1]

def divisionPolynomialRep (E : WeierstrassCurve k) (n : ℕ) (x : k) : Fin 2 → k :=
  ![(E.Φ (n : ℤ)).eval x, (E.ΨSq (n : ℤ)).eval x]

@[simp] theorem divisionPolynomialRep_zero (E : WeierstrassCurve k) (x : k) :
    divisionPolynomialRep E 0 x = ![1, 0] := by
  funext i
  fin_cases i <;> simp [divisionPolynomialRep]

@[simp] theorem divisionPolynomialRep_one (E : WeierstrassCurve k) (x : k) :
    divisionPolynomialRep E 1 x = ![x, 1] := by
  funext i
  fin_cases i <;> simp [divisionPolynomialRep]

theorem symmetricPair2_ne_zero {u v : Fin 2 → k} (hu : u ≠ 0) (hv : v ≠ 0) :
    symmetricPair2 u v ≠ 0 := by
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro hu1
      apply hu
      funext i
      fin_cases i <;> assumption
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        funext i
        fin_cases i <;> assumption
      intro hzero
      have h2 := congrFun hzero (2 : Fin 3)
      simp [symmetricPair2, hu1, hv1] at h2
    · intro hzero
      have h1 := congrFun hzero (1 : Fin 3)
      simp [symmetricPair2, hu0, hu1, hv0] at h1
  · by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        funext i
        fin_cases i <;> assumption
      intro hzero
      have h1 := congrFun hzero (1 : Fin 3)
      simp [symmetricPair2, hu0, hv0, hv1] at h1
    · intro hzero
      have h0 := congrFun hzero (0 : Fin 3)
      simp [symmetricPair2, hu0, hv0] at h0

theorem symmetricPair2_zero_left (v : Fin 2 → k) :
    symmetricPair2 (0 : Fin 2 → k) v = 0 := by
  funext i
  fin_cases i <;> simp [symmetricPair2]

theorem addSubMap_eval_symmetricPair2
    (E : WeierstrassCurve k) [E.IsElliptic] (u v : Fin 2 → k) :
    (fun i ↦ (E.addSubMap i).eval (symmetricPair2 u v)) =
      ![kummerBiquadraticHomogeneous E (u 0) (u 1) (v 0) (v 1),
        kummerBiquadraticMiddleHomogeneous E (u 0) (u 1) (v 0) (v 1),
        (u 0 * v 1 - u 1 * v 0) ^ 2] := by
  funext i
  fin_cases i <;>
    simp [symmetricPair2, WeierstrassCurve.addSubMap,
      kummerBiquadraticHomogeneous, kummerBiquadraticMiddleHomogeneous] <;>
    ring

theorem addSubMap_divisionPolynomialRep_step
    (E : WeierstrassCurve k) [E.IsElliptic] (x : k) (m : ℕ) :
    (fun i ↦ (E.addSubMap i).eval
      (symmetricPair2 (divisionPolynomialRep E (m + 1) x)
        (divisionPolynomialRep E 1 x))) =
      symmetricPair2 (divisionPolynomialRep E (m + 2) x)
        (divisionPolynomialRep E m x) := by
  have hproduct := congrArg (Polynomial.eval x)
    (kummerDivisionPolynomialRecurrence_nat E (m + 1))
  have hmiddle := congrArg (Polynomial.eval x)
    (kummerDivisionPolynomialMiddleRecurrence_nat E (m + 1))
  have hgap := congrArg (Polynomial.eval x)
    (divisionPolynomialDifference_sq E (m + 1 : ℕ))
  simp only [eval_kummerBiquadraticPolynomial, Polynomial.eval_mul] at hproduct
  simp only [eval_kummerBiquadraticMiddlePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul] at hmiddle
  simp only [divisionPolynomialDifference, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X] at hgap
  have hi0 : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
  have hi2 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by omega
  rw [hi0, hi2] at hproduct hmiddle hgap
  have hgap' :
      ((E.Φ (m + 1 : ℕ)).eval x - (E.ΨSq (m + 1 : ℕ)).eval x * x) ^ 2 =
        (E.ΨSq (m + 2 : ℕ)).eval x * (E.ΨSq (m : ℕ)).eval x := by
    calc
      _ = (x * (E.ΨSq (m + 1 : ℕ)).eval x -
          (E.Φ (m + 1 : ℕ)).eval x) ^ 2 := by ring
      _ = _ := hgap
  rw [addSubMap_eval_symmetricPair2 E]
  funext i
  fin_cases i
  · simpa [symmetricPair2, divisionPolynomialRep,
      kummerBiquadraticHomogeneous] using hproduct
  · simpa [symmetricPair2, divisionPolynomialRep,
      kummerBiquadraticMiddleHomogeneous] using hmiddle
  · simpa [symmetricPair2, divisionPolynomialRep] using hgap'

theorem divisionPolynomialRep_ne_zero
    (E : WeierstrassCurve k) [E.IsElliptic] (x : k) (n : ℕ) :
    divisionPolynomialRep E n x ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ m =>
          have hinput :
              symmetricPair2 (divisionPolynomialRep E (m + 1) x)
                (divisionPolynomialRep E 1 x) ≠ 0 :=
            symmetricPair2_ne_zero ih (by simp)
          have hout := E.addSubMap_ne_zero hinput
          rw [addSubMap_divisionPolynomialRep_step E x m] at hout
          intro hzero
          apply hout
          rw [hzero, symmetricPair2_zero_left]

def ProjectivelyEquivalent2 (u v : Fin 2 → k) : Prop :=
  u 0 * v 1 = u 1 * v 0

theorem projectivelyEquivalent2_eq_scale {u v : Fin 2 → k}
    (h : ProjectivelyEquivalent2 u v) (hv : v ≠ 0) :
    ∃ c : k, u = fun i ↦ c * v i := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      funext i
      fin_cases i <;> assumption
    have hu0 : u 0 = 0 := by
      apply (mul_right_cancel₀ hv1)
      simpa [ProjectivelyEquivalent2, hv0] using h
    refine ⟨u 1 / v 1, ?_⟩
    funext i
    fin_cases i <;> simp_all [ProjectivelyEquivalent2]
  · refine ⟨u 0 / v 0, ?_⟩
    funext i
    fin_cases i <;> simp_all [ProjectivelyEquivalent2, div_eq_mul_inv]
    field_simp
    simpa [mul_comm] using h.symm

theorem symmetricPair2_scale_left (c : k) (u v : Fin 2 → k) :
    symmetricPair2 (fun i ↦ c * u i) v = fun i ↦ c * symmetricPair2 u v i := by
  funext i
  fin_cases i <;> simp [symmetricPair2] <;> ring

theorem symmetricPair2_scale_right (c : k) (u v : Fin 2 → k) :
    symmetricPair2 u (fun i ↦ c * v i) = fun i ↦ c * symmetricPair2 u v i := by
  funext i
  fin_cases i <;> simp [symmetricPair2] <;> ring

theorem symmetricPair2_projective_cancel_fixed_right
    {a c d : Fin 2 → k} (hd : d ≠ 0)
    (hpair : ProjectivelyEquivalent3 (symmetricPair2 a d) (symmetricPair2 c d)) :
    ProjectivelyEquivalent2 a c := by
  by_cases hd0 : d 0 = 0
  · have hd1 : d 1 ≠ 0 := by
      intro hd1
      apply hd
      funext i
      fin_cases i <;> assumption
    have hp := hpair (1 : Fin 3) (2 : Fin 3)
    simp [symmetricPair2, hd0] at hp
    apply mul_left_cancel₀ (pow_ne_zero 2 hd1)
    linear_combination hp
  · have hp := hpair (0 : Fin 3) (1 : Fin 3)
    simp [symmetricPair2] at hp
    apply mul_left_cancel₀ (pow_ne_zero 2 hd0)
    linear_combination hp

theorem symmetricPair2_projective_cancel_right
    {a b c d : Fin 2 → k} (hb : b ≠ 0) (hd : d ≠ 0)
    (hbd : ProjectivelyEquivalent2 b d)
    (hpair : ProjectivelyEquivalent3 (symmetricPair2 a b) (symmetricPair2 c d)) :
    ProjectivelyEquivalent2 a c := by
  obtain ⟨s, rfl⟩ := projectivelyEquivalent2_eq_scale hbd hd
  have hs : s ≠ 0 := by
    intro hs
    apply hb
    funext i
    simp [hs]
  have hpair' : ProjectivelyEquivalent3 (symmetricPair2 a d) (symmetricPair2 c d) := by
    intro i j
    have hij := hpair i j
    rw [symmetricPair2_scale_right] at hij
    apply mul_left_cancel₀ hs
    simpa only [mul_assoc] using hij
  exact symmetricPair2_projective_cancel_fixed_right hd hpair'

theorem point_sym2x_eq_symmetricPair2
    {W : WeierstrassCurve.Affine k} (P Q : W.Point) :
    P.sym2x Q = symmetricPair2 P.xRep Q.xRep := by
  cases P <;> cases Q <;>
    simp [symmetricPair2, ← WeierstrassCurve.Affine.Point.zero_def]

theorem addSubMap_eval_scale
    (E : WeierstrassCurve k) [E.IsElliptic] (s : k) (v : Fin 3 → k) :
    (fun i ↦ (E.addSubMap i).eval (fun j ↦ s * v j)) =
      fun i ↦ s ^ 2 * (E.addSubMap i).eval v := by
  funext i
  fin_cases i <;> simp [WeierstrassCurve.addSubMap] <;> ring

theorem divisionPolynomialXProjective_step
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : (E⁄k).Nonsingular x y) (m : ℕ)
    (hcur : ProjectivelyEquivalent2
      (((m + 1 : ℕ) : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)).xRep
      (divisionPolynomialRep E (m + 1) x))
    (hprev : ProjectivelyEquivalent2
      ((m : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)).xRep
      (divisionPolynomialRep E m x)) :
    ProjectivelyEquivalent2
      (((m + 2 : ℕ) : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)).xRep
      (divisionPolynomialRep E (m + 2) x) := by
  let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x y h
  let Qcur : (E⁄k).Point := ((m + 1 : ℕ) : ℤ) • P
  let Qprev : (E⁄k).Point := (m : ℤ) • P
  let Qnext : (E⁄k).Point := ((m + 2 : ℕ) : ℤ) • P
  let vcur := divisionPolynomialRep E (m + 1) x
  let vprev := divisionPolynomialRep E m x
  let vnext := divisionPolynomialRep E (m + 2) x
  have hvcur : vcur ≠ 0 := divisionPolynomialRep_ne_zero E x (m + 1)
  have hvprev : vprev ≠ 0 := divisionPolynomialRep_ne_zero E x m
  have hcur' : ProjectivelyEquivalent2 Qcur.xRep vcur := by
    simpa only [Qcur, P, vcur] using hcur
  have hprev' : ProjectivelyEquivalent2 Qprev.xRep vprev := by
    simpa only [Qprev, P, vprev] using hprev
  obtain ⟨c, hcscale⟩ := projectivelyEquivalent2_eq_scale hcur' hvcur
  have hQcur : Qcur.xRep ≠ 0 :=
    WeierstrassCurve.Affine.Point.xRep_ne_zero Qcur
  have hc : c ≠ 0 := by
    intro hc
    apply hQcur
    rw [hc] at hcscale
    funext i
    simpa using congrFun hcscale i
  have hPx : P.xRep = divisionPolynomialRep E 1 x := by
    simp [P, divisionPolynomialRep]
  have hinput : Qcur.sym2x P =
      fun i ↦ c * symmetricPair2 vcur (divisionPolynomialRep E 1 x) i := by
    rw [point_sym2x_eq_symmetricPair2, hcscale, hPx,
      symmetricPair2_scale_left]
  have hpoly := addSubMap_divisionPolynomialRep_step E x m
  have hout :
      (fun i ↦ (E.addSubMap i).eval (Qcur.sym2x P)) =
        fun i ↦ c ^ 2 * symmetricPair2 vnext vprev i := by
    rw [hinput, addSubMap_eval_scale]
    simpa only [vcur, vnext, vprev] using congrArg (fun z ↦ fun i ↦ c ^ 2 * z i) hpoly
  have hplus : Qcur + P = Qnext := by
    dsimp only [Qcur, Qnext]
    calc
      ((m + 1 : ℕ) : ℤ) • P + P =
          ((m + 1 : ℕ) : ℤ) • P + (1 : ℤ) • P := by simp
      _ = (((m + 1 : ℕ) : ℤ) + 1) • P := (add_zsmul P _ _).symm
      _ = ((m + 2 : ℕ) : ℤ) • P := by
        congr 1
  have hminus : Qcur - P = Qprev := by
    dsimp only [Qcur, Qprev]
    calc
      ((m + 1 : ℕ) : ℤ) • P - P =
          ((m + 1 : ℕ) : ℤ) • P - (1 : ℤ) • P := by simp
      _ = (((m + 1 : ℕ) : ℤ) - 1) • P := (sub_zsmul P _ _).symm
      _ = (m : ℤ) • P := by
        congr 1
        omega
  have hpoint := addSubMap_sym2x_projective E Qcur P
  have hpoint' : ProjectivelyEquivalent3
      (fun i ↦ (E.addSubMap i).eval (Qcur.sym2x P))
      (symmetricPair2 Qnext.xRep Qprev.xRep) := by
    rw [← point_sym2x_eq_symmetricPair2, ← hplus, ← hminus]
    exact hpoint
  have hscaled : ProjectivelyEquivalent3
      (symmetricPair2 Qnext.xRep Qprev.xRep)
      (fun i ↦ c ^ 2 * symmetricPair2 vnext vprev i) := by
    rw [← hout]
    exact hpoint'.symm
  have hpair : ProjectivelyEquivalent3
      (symmetricPair2 Qnext.xRep Qprev.xRep)
      (symmetricPair2 vnext vprev) := by
    intro i j
    have hij := hscaled i j
    apply mul_right_cancel₀ (pow_ne_zero 2 hc)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hij
  exact symmetricPair2_projective_cancel_right
    (WeierstrassCurve.Affine.Point.xRep_ne_zero Qprev) hvprev hprev' hpair

theorem divisionPolynomialXProjective_nat
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : (E⁄k).Nonsingular x y) (n : ℕ) :
    ProjectivelyEquivalent2
      ((n : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)).xRep
      (divisionPolynomialRep E n x) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [ProjectivelyEquivalent2, divisionPolynomialRep,
        WeierstrassCurve.Affine.Point.xRep]
  | one =>
      simp [ProjectivelyEquivalent2, divisionPolynomialRep,
        WeierstrassCurve.Affine.Point.xRep]
  | more m hm hm1 =>
      exact divisionPolynomialXProjective_step E h m hm1 hm

theorem divisionPolynomialXHomogeneous_nat
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    DivisionPolynomialXHomogeneous E n := by
  intro x y h
  simpa only [DivisionPolynomialXHomogeneous, ProjectivelyEquivalent2,
    divisionPolynomialRep, Matrix.cons_val_zero, Matrix.cons_val_one]
    using divisionPolynomialXProjective_nat E h n

theorem divisionPolynomialXRelation_nat
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    DivisionPolynomialXRelation E n :=
  xRelation_of_xHomogeneous E (divisionPolynomialXHomogeneous_nat E n)

theorem psiSqDetectsNTorsion_nat
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    PsiSqDetectsNTorsion E n :=
  psiSqDetectsNTorsion_of_xRelation E (divisionPolynomialXRelation_nat E n)

/-- Finiteness of rational `n`-torsion in the characteristic-prime-to-`n` lane. The remaining
all-characteristic provider theorem needs a separate argument when `(n : k) = 0`. -/
theorem n_torsion_finite_prime_to_char
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) : Finite (E.nTorsion n) :=
  n_torsion_finite_of_psiSq_detection E hn (psiSqDetectsNTorsion_nat E n)

end

end FLTMethodology.Torsion
