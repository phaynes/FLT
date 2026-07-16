/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLT.EllipticCurve.Torsion
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.WithTopBot

/-!
# Source boundary for finite elliptic-curve torsion

This file isolates the missing division-polynomial dictionary from the elementary finiteness
assembly. A nonzero polynomial that detects the x-coordinate of every nonzero `n`-torsion point
has finitely many roots. Above each root, the Weierstrass equation is a nonzero quadratic in the
y-coordinate. Consequently the `n`-torsion subtype is finite.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

def fiberPolynomial (E : WeierstrassCurve k) (x : k) : k[X] :=
  X ^ 2 + C (E.a₁ * x + E.a₃) * X +
    C (-(x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆))

lemma fiberPolynomial_ne_zero (E : WeierstrassCurve k) (x : k) :
    fiberPolynomial E x ≠ 0 := by
  exact (isMonicOfDegree_add_add_two
    (E.a₁ * x + E.a₃)
    (-(x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆))).monic.ne_zero

lemma equation_iff_eval_fiberPolynomial (E : WeierstrassCurve k) (x y : k) :
    E.toAffine.Equation x y ↔ (fiberPolynomial E x).eval y = 0 := by
  rw [E.toAffine.equation_iff]
  rw [show (fiberPolynomial E x).eval y =
      y ^ 2 + E.a₁ * x * y + E.a₃ * y -
        (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) by
    simp only [fiberPolynomial, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring]
  exact sub_eq_zero.symm

structure TorsionXDetector (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) where
  polynomial : k[X]
  polynomial_ne_zero : polynomial ≠ 0
  detects : ∀ {x y : k} (h : E.toAffine.Nonsingular x y),
    (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0 →
      polynomial.eval x = 0

def detectedAffineSet (E : WeierstrassCurve k) (f : k[X]) : Set (k × k) :=
  {xy | f.eval xy.1 = 0 ∧ E.toAffine.Equation xy.1 xy.2}

lemma detectedAffineSet_finite (E : WeierstrassCurve k) (f : k[X]) (hf : f ≠ 0) :
    (detectedAffineSet E f).Finite := by
  apply Set.Finite.of_finite_fibers Prod.fst
  · refine (Polynomial.rootSet_finite f k).subset ?_
    rintro x ⟨⟨x', y⟩, hxy, rfl⟩
    exact (Polynomial.mem_rootSet_of_ne hf).2 hxy.1
  · rintro x ⟨⟨x', y'⟩, hxy, hxx⟩
    refine ((Set.finite_singleton x).prod
      (Polynomial.rootSet_finite (fiberPolynomial E x) k)).subset ?_
    rintro ⟨a, b⟩ ⟨hab, ha⟩
    have hax : a = x := by simpa using ha
    subst a
    refine ⟨by simp, (Polynomial.mem_rootSet_of_ne
      (fiberPolynomial_ne_zero E x)).2 ?_⟩
    exact (equation_iff_eval_fiberPolynomial E x b).mp hab.2

theorem n_torsion_finite_of_detector
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (D : TorsionXDetector E n) : Finite (E.nTorsion n) := by
  let S := detectedAffineSet E D.polynomial
  have hS : S.Finite := detectedAffineSet_finite E D.polynomial D.polynomial_ne_zero
  letI : Finite S := hS
  let T := {xy : k × k // ∃ h : E.toAffine.Nonsingular xy.1 xy.2,
    WeierstrassCurve.Affine.Point.some xy.1 xy.2 h ∈
      Submodule.torsionBy ℤ (E⁄k).Point n}
  let encode : T → S := fun xy ↦
    ⟨xy.1, by
      obtain ⟨h, htors⟩ := xy.2
      refine ⟨D.detects h ?_, E.toAffine.equation_iff_nonsingular.mpr h⟩
      exact (Submodule.mem_torsionBy_iff _ _).mp htors⟩
  have hencode : Function.Injective encode := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : k × k)) h
  letI : Finite T := Finite.of_injective encode hencode
  letI : Finite (WithZero T) := by
    change Finite (Option T)
    infer_instance
  let e := WeierstrassCurve.Affine.nonsingularPointEquivSubtype
    (W' := E.toAffine)
    (p := fun P ↦ P ∈ Submodule.torsionBy ℤ (E⁄k).Point n)
    (show (0 : (E⁄k).Point) ∈ Submodule.torsionBy ℤ (E⁄k).Point n by simp)
  exact Finite.of_equiv (WithZero T) e.symm

/-- The exact missing point/division-polynomial dictionary in the characteristic-prime-to-`n`
lane. Mathlib already supplies `ΨSq`, its degree, and its nonvanishing under the same hypothesis. -/
def PsiSqDetectsNTorsion
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop :=
  ∀ {x y : k} (h : E.toAffine.Nonsingular x y),
    (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0 →
      (E.ΨSq (n : ℤ)).eval x = 0

def psiSqTorsionXDetector
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    TorsionXDetector E n where
  polynomial := E.ΨSq (n : ℤ)
  polynomial_ne_zero := E.ΨSq_ne_zero (by simpa using hn)
  detects := hdetect

/-- The exact nonzero-denominator x-coordinate formula needed from division polynomials. Proving
this uniformly in `n` is sufficient for the detector theorem, without requiring the converse
statement that every division-polynomial root is torsion. -/
def DivisionPolynomialXFormula
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop :=
  ∀ {x y : k} (h : E.toAffine.Nonsingular x y),
    (E.ΨSq (n : ℤ)).eval x ≠ 0 →
      ∃ (yn : k) (hn : E.toAffine.Nonsingular
          ((E.Φ (n : ℤ)).eval x / (E.ΨSq (n : ℤ)).eval x) yn),
        (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) =
          WeierstrassCurve.Affine.Point.some
            ((E.Φ (n : ℤ)).eval x / (E.ΨSq (n : ℤ)).eval x) yn hn

theorem psiSqDetectsNTorsion_of_xFormula
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hx : DivisionPolynomialXFormula E n) : PsiSqDetectsNTorsion E n := by
  intro x y h htorsion
  by_contra hpsi
  obtain ⟨yn, hn, hpoint⟩ := hx h hpsi
  rw [htorsion] at hpoint
  exact WeierstrassCurve.Affine.Point.some_ne_zero hn hpoint.symm

/-- A denominator-free x-coordinate relation which includes the point-at-infinity branch. This is
the recurrence-friendly form of `DivisionPolynomialXFormula`: it records `ΨSq = 0` when the
multiple is infinity and otherwise records `x(nP) * ΨSq = Φ`. -/
def DivisionPolynomialXRelation
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop :=
  ∀ {x y : k} (h : E.toAffine.Nonsingular x y),
    match (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) with
    | .zero => (E.ΨSq (n : ℤ)).eval x = 0
    | .some xn _ _ => xn * (E.ΨSq (n : ℤ)).eval x = (E.Φ (n : ℤ)).eval x

theorem psiSqDetectsNTorsion_of_xRelation
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hr : DivisionPolynomialXRelation E n) : PsiSqDetectsNTorsion E n := by
  intro x y h htorsion
  have hrel := hr h
  rw [htorsion] at hrel
  exact hrel

theorem divisionPolynomialXFormula_of_xRelation
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hr : DivisionPolynomialXRelation E n) : DivisionPolynomialXFormula E n := by
  intro x y h hpsi
  have hrel := hr h
  generalize hpoint : (n : ℤ) •
      (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = Q at hrel
  cases Q with
  | zero =>
      exact (hpsi hrel).elim
  | some xn yn hn =>
      have hx : xn = (E.Φ (n : ℤ)).eval x / (E.ΨSq (n : ℤ)).eval x :=
        (eq_div_iff hpsi).2 hrel
      have hnE : E.toAffine.Nonsingular xn yn := by
        change E.toAffine.Nonsingular xn yn at hn
        exact hn
      refine ⟨yn, hx ▸ hnE, ?_⟩
      cases hx
      rfl

theorem divisionPolynomialXRelation_zero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXRelation E 0 := by
  intro x y h
  change (E.ΨSq 0).eval x = 0
  simp

theorem divisionPolynomialXRelation_one
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXRelation E 1 := by
  intro x y h
  change x * (E.ΨSq 1).eval x = (E.Φ 1).eval x
  simp

theorem divisionPolynomialXFormula_zero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXFormula E 0 :=
  divisionPolynomialXFormula_of_xRelation E (divisionPolynomialXRelation_zero E)

theorem divisionPolynomialXFormula_one
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXFormula E 1 :=
  divisionPolynomialXFormula_of_xRelation E (divisionPolynomialXRelation_one E)

/-- The biquadratic x-only expression used by differential addition on a generalized Weierstrass
curve. -/
def kummerBiquadratic (E : WeierstrassCurve k) (x₁ x₂ : k) : k :=
  x₁ ^ 2 * x₂ ^ 2 - E.b₄ * x₁ * x₂ - E.b₆ * (x₁ + x₂) - E.b₈

/-- The x-only differential-addition product for two affine points with distinct x-coordinates.
It removes the need for a separate y-coordinate division polynomial in the scalar recurrence. -/
theorem addX_mul_addNegX_kummer
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x₁ x₂ y₁ y₂ : k} (h₁ : E.toAffine.Nonsingular x₁ y₁)
    (h₂ : E.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    let xplus := E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)
    let xminus := E.toAffine.addX x₁ x₂
      (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))
    xplus * xminus * (x₁ - x₂) ^ 2 = kummerBiquadratic E x₁ x₂ := by
  dsimp only [kummerBiquadratic]
  rw [E.toAffine.slope_of_X_ne hx]
  rw [E.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [sub_ne_zero.mpr hx]
  have heq₁ := h₁.1
  have heq₂ := h₂.1
  rw [E.toAffine.equation_iff] at heq₁ heq₂
  simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination
    (E.a₁ ^ 2 * x₁ * x₂ - E.a₁ ^ 2 * x₂ ^ 2 + E.a₁ * E.a₃ * x₁ -
      E.a₁ * E.a₃ * x₂ + E.a₁ * x₁ * y₁ + 2 * E.a₁ * x₂ * y₂ -
      E.a₂ * x₁ ^ 2 + 4 * E.a₂ * x₁ * x₂ - 6 * E.a₂ * x₂ ^ 2 +
      E.a₃ * y₁ + 2 * E.a₃ * y₂ + E.a₄ * x₁ - 4 * E.a₄ * x₂ - 3 * E.a₆ -
      x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 6 * x₂ ^ 3 +
      y₁ ^ 2 + 2 * y₂ ^ 2) * heq₁ +
    (-E.a₁ ^ 2 * x₁ ^ 2 + E.a₁ ^ 2 * x₁ * x₂ - E.a₁ * E.a₃ * x₁ +
      E.a₁ * E.a₃ * x₂ - 4 * E.a₁ * x₁ * y₁ + E.a₁ * x₂ * y₂ +
      4 * E.a₂ * x₁ * x₂ - E.a₂ * x₂ ^ 2 - 4 * E.a₃ * y₁ + E.a₃ * y₂ +
      2 * E.a₄ * x₁ + E.a₄ * x₂ + 3 * E.a₆ + 2 * x₁ ^ 2 * x₂ +
      2 * x₁ * x₂ ^ 2 - x₂ ^ 3 - 4 * y₁ ^ 2 + y₂ ^ 2) * heq₂

theorem psiSq_two_eval_eq_negY_gap_sq
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : E.toAffine.Nonsingular x y) :
    (E.ΨSq 2).eval x = (y - E.toAffine.negY x y) ^ 2 := by
  rw [E.ΨSq_two, WeierstrassCurve.Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  have heq := h.1
  rw [E.toAffine.equation_iff] at heq
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * heq

/-- The exact division-polynomial x-coordinate contract at `n = 2`. Besides validating the
contract against Mathlib's affine group law, this exposes the algebraic shape required by the
uniform recurrence proof. -/
theorem divisionPolynomialXFormula_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXFormula E 2 := by
  intro x y h hpsi
  have hgap : y - E.toAffine.negY x y ≠ 0 := by
    intro hzero
    apply hpsi
    change (E.ΨSq 2).eval x = 0
    rw [psiSq_two_eval_eq_negY_gap_sq E h, hzero, zero_pow two_ne_zero]
  have hyne : y ≠ E.toAffine.negY x y := sub_ne_zero.mp hgap
  let ell : k := (E⁄k).slope x x y y
  let x₂ : k := (E⁄k).addX x x ell
  let y₂ : k := (E⁄k).addY x x y ell
  let h₂ : (E⁄k).Nonsingular x₂ y₂ :=
    WeierstrassCurve.Affine.nonsingular_add h h (fun hxy ↦ hyne hxy.2)
  have hx₂ : x₂ = (E.Φ 2).eval x / (E.ΨSq 2).eval x := by
    rw [psiSq_two_eval_eq_negY_gap_sq E h]
    rw [eq_div_iff (pow_ne_zero 2 hgap)]
    simp only [x₂, ell, WeierstrassCurve.Affine.addX]
    have hyne' : y ≠ (E⁄k).negY x y := by
      simpa [WeierstrassCurve.baseChange] using hyne
    rw [(E⁄k).slope_of_Y_ne rfl hyne']
    simp only [WeierstrassCurve.Affine.negY]
    simp [WeierstrassCurve.baseChange]
    have hden₁ : y - (-y - E.a₁ * x - E.a₃) ≠ 0 := by
      simpa [WeierstrassCurve.Affine.negY] using hgap
    have hden₂ : y - (-y - x * E.a₁ - E.a₃) ≠ 0 := by
      simpa only [mul_comm x E.a₁] using hden₁
    field_simp [hden₁, hden₂]
    have heq := h.1
    rw [E.toAffine.equation_iff] at heq
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination -(E.a₁ ^ 2 + 4 * E.a₂ + 8 * x) * heq
  have h₂E : E.toAffine.Nonsingular x₂ y₂ := by
    change E.toAffine.Nonsingular x₂ y₂ at h₂
    exact h₂
  refine ⟨y₂, hx₂ ▸ h₂E, ?_⟩
  have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (W := E⁄k) (h₁ := h) hyne
  calc
    (2 : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) =
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
          (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) := by
            rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, natCast_zsmul, two_nsmul]
    _ = WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
      simpa only [x₂, y₂, ell, h₂] using hadd
    _ = WeierstrassCurve.Affine.Point.some
          ((E.Φ (2 : ℤ)).eval x / (E.ΨSq (2 : ℤ)).eval x) y₂
          (hx₂ ▸ h₂E) := by
      simpa only [WeierstrassCurve.Affine.Point.some.injEq, and_true] using hx₂

theorem divisionPolynomialXRelation_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXRelation E 2 := by
  intro x y h
  by_cases hpsi : (E.ΨSq (2 : ℤ)).eval x = 0
  · have hgapSq : (y - E.toAffine.negY x y) ^ 2 = 0 := by
      rw [← psiSq_two_eval_eq_negY_gap_sq E h]
      exact hpsi
    have hy : y = E.toAffine.negY x y := by
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hgapSq)
    change
      match
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
          (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)
      with
      | .zero => (E.ΨSq (2 : ℤ)).eval x = 0
      | .some xn _ _ => xn * (E.ΨSq (2 : ℤ)).eval x = (E.Φ (2 : ℤ)).eval x
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := E⁄k) hy]
    exact hpsi
  · obtain ⟨yn, hn, hpoint⟩ := divisionPolynomialXFormula_two E h hpsi
    rw [hpoint]
    change
      ((E.Φ (2 : ℤ)).eval x / (E.ΨSq (2 : ℤ)).eval x) *
        (E.ΨSq (2 : ℤ)).eval x = (E.Φ (2 : ℤ)).eval x
    exact div_mul_cancel₀ _ hpsi

theorem psiSqDetectsNTorsion_zero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 0 := by
  intro x _ _ _
  change (E.ΨSq 0).eval x = 0
  simp

theorem psiSqDetectsNTorsion_one
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 1 := by
  intro _ _ h hone
  have hpzero :
      (WeierstrassCurve.Affine.Point.some _ _ h : (E⁄k).Point) = 0 := by
    change (WeierstrassCurve.Affine.Point.some _ _ h : (E⁄k).Point) = 0 at hone
    exact hone
  exact (WeierstrassCurve.Affine.Point.some_ne_zero h hpzero).elim

/-- The detector interface agrees with Mathlib's affine group law and division-polynomial
normalization in the first nontrivial case. This validates the boundary but does not supply the
general point/division-polynomial recurrence. -/
theorem psiSqDetectsNTorsion_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 2 := by
  intro x y h htwo
  have htwo' :
      (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0 := by
    change
      (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0 at htwo
    exact htwo
  have hy : y = E.toAffine.negY x y := by
    by_contra hne
    have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := E⁄k) (h₁ := h) hne
    rw [hadd] at htwo'
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ htwo'
  change (E.ΨSq 2).eval x = 0
  rw [E.ΨSq_two]
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  have heq := h.1
  rw [E.toAffine.equation_iff] at heq
  simp only [WeierstrassCurve.Affine.negY] at hy
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  have hlin : 2 * y + E.a₁ * x + E.a₃ = 0 := by
    linear_combination hy
  linear_combination (2 * y + E.a₁ * x + E.a₃) * hlin - 4 * heq

/-- The next detector case exercises affine doubling and confirms that Mathlib's tangent formula
and `Ψ₃` normalization agree. -/
theorem psiSqDetectsNTorsion_three
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 3 := by
  intro x y h hthree
  let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x y h
  have hthreeP : (3 : ℕ) • P = 0 := by
    simpa only [P, Int.ofNat_eq_natCast, natCast_zsmul] using hthree
  have hthree' : (P + P) + P = 0 := by
    rw [three'_nsmul] at hthreeP
    exact hthreeP
  have hdouble : P + P = -P := add_eq_zero_iff_eq_neg.mp hthree'
  have hyne : y ≠ E.toAffine.negY x y := by
    intro hy
    have hpp0 : P + P = 0 := by
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := E⁄k) hy
    have hnegzero : -P = 0 := hdouble.symm.trans hpp0
    have hpzero : P = 0 := neg_eq_zero.mp hnegzero
    exact WeierstrassCurve.Affine.Point.some_ne_zero h hpzero
  have hxadd :
      E.toAffine.addX x x (E.toAffine.slope x x y y) = x := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := E⁄k) hyne] at hdouble
    simp only [P, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq] at hdouble
    exact hdouble.1
  rw [E.toAffine.slope_of_Y_ne rfl hyne] at hxadd
  have hden : y - E.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hyne
  simp only [WeierstrassCurve.Affine.addX] at hxadd
  field_simp [hden] at hxadd
  change (E.ΨSq 3).eval x = 0
  rw [E.ΨSq_three]
  rw [Polynomial.eval_pow, sq_eq_zero_iff]
  rw [WeierstrassCurve.Ψ₃]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
  have heq := h.1
  rw [E.toAffine.equation_iff] at heq
  simp only [WeierstrassCurve.Affine.negY] at hxadd
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination -hxadd -
    (E.a₁ ^ 2 + 4 * E.a₂ + 12 * x) * heq

/-- The explicit `ψ₄ / ψ₂` doubling identity at an affine non-two-torsion point. -/
theorem prePsiFour_eval_eq_psiTwo_double
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : E.toAffine.Nonsingular x y)
    (hyne : y ≠ E.toAffine.negY x y) :
    let ell : k := (E⁄k).slope x x y y
    let x₂ : k := (E⁄k).addX x x ell
    let y₂ : k := (E⁄k).addY x x y ell
    (E.preΨ₄).eval x = (y - E.toAffine.negY x y) ^ 3 *
      (2 * y₂ + E.a₁ * x₂ + E.a₃) := by
  dsimp only
  have hden : y - E.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hyne
  have hyne' : y ≠ (E⁄k).negY x y := by
    simpa [WeierstrassCurve.baseChange] using hyne
  rw [WeierstrassCurve.preΨ₄]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX]
  rw [(E⁄k).slope_of_Y_ne rfl hyne']
  simp only [WeierstrassCurve.Affine.negY]
  simp [WeierstrassCurve.baseChange]
  have hde : y - (-y - x * E.toAffine.a₁ - E.toAffine.a₃) ≠ 0 := by
    convert hden using 1
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hd : x * E.a₁ + E.a₃ + y * 2 ≠ 0 := by
    intro hz
    apply hden
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination hz
  field_simp [hde, hd]
  have heq := h.1
  rw [E.toAffine.equation_iff] at heq
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination
    (8 * (4 * (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) +
          (E.a₁ * x + E.a₃) ^ 2) -
      (2 * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄) +
          E.a₁ * (E.a₁ * x + E.a₃)) *
        (E.a₁ ^ 2 + 4 * E.a₂ + 12 * x) +
      16 * (y ^ 2 + E.a₁ * x * y + E.a₃ * y -
        (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆))) * heq

/-- The first recursive even detector case. -/
theorem psiSqDetectsNTorsion_four
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 4 := by
  intro x y h hfour
  let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x y h
  have hfourN : (4 : ℕ) • P = 0 := by
    simpa only [P, Int.ofNat_eq_natCast, natCast_zsmul] using hfour
  by_cases htwo : P + P = 0
  · have hpsi₂ : E.Ψ₂Sq.eval x = 0 := by
      rw [← E.ΨSq_two]
      apply psiSqDetectsNTorsion_two E h
      change P + P = 0
      exact htwo
    change (E.ΨSq 4).eval x = 0
    rw [E.ΨSq_four]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, hpsi₂, mul_zero]
  · have hyne : y ≠ E.toAffine.negY x y := by
      intro hy
      apply htwo
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := E⁄k) hy
    let ell : k := (E⁄k).slope x x y y
    let x₂ : k := (E⁄k).addX x x ell
    let y₂ : k := (E⁄k).addY x x y ell
    let h₂ : (E⁄k).Nonsingular x₂ y₂ :=
      WeierstrassCurve.Affine.nonsingular_add h h (fun hxy ↦ hyne hxy.2)
    let Q : (E⁄k).Point :=
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
    have hPQ : P + P = Q := by
      simpa only [P, Q, h₂, x₂, y₂, ell] using
        (WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := E⁄k) hyne)
    have hQQ : Q + Q = 0 := by
      have h22 : (2 : ℕ) • ((2 : ℕ) • P) = 0 := by
        rw [← mul_nsmul]
        norm_num
        exact hfourN
      simpa only [two_nsmul, hPQ] using h22
    have hy₂ : y₂ = E.toAffine.negY x₂ y₂ := by
      by_contra hy₂ne
      have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
        (W := E⁄k) (h₁ := h₂) hy₂ne
      rw [hadd] at hQQ
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hQQ
    have hpsi₂Q : 2 * y₂ + E.a₁ * x₂ + E.a₃ = 0 := by
      simp only [WeierstrassCurve.Affine.negY] at hy₂
      linear_combination hy₂
    have hpre : (E.preΨ₄).eval x = 0 := by
      have hid : (E.preΨ₄).eval x =
          (y - E.toAffine.negY x y) ^ 3 *
            (2 * y₂ + E.a₁ * x₂ + E.a₃) := by
        simpa only [ell, x₂, y₂] using prePsiFour_eval_eq_psiTwo_double E h hyne
      rw [hid, hpsi₂Q, mul_zero]
    change (E.ΨSq 4).eval x = 0
    rw [E.ΨSq_four]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, hpre, zero_pow two_ne_zero,
      zero_mul]

theorem n_torsion_finite_of_psiSq_detection
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    Finite (E.nTorsion n) :=
  n_torsion_finite_of_detector E (psiSqTorsionXDetector E hn hdetect)

#check n_torsion_finite_of_detector
#check n_torsion_finite_of_psiSq_detection
#check DivisionPolynomialXFormula
#check psiSqDetectsNTorsion_of_xFormula
#check psiSq_two_eval_eq_negY_gap_sq
#check divisionPolynomialXFormula_two
#check DivisionPolynomialXRelation
#check psiSqDetectsNTorsion_of_xRelation
#check divisionPolynomialXFormula_of_xRelation
#check divisionPolynomialXRelation_zero
#check divisionPolynomialXRelation_one
#check divisionPolynomialXRelation_two
#check divisionPolynomialXFormula_zero
#check divisionPolynomialXFormula_one
#check kummerBiquadratic
#check addX_mul_addNegX_kummer
#check psiSqDetectsNTorsion_zero
#check psiSqDetectsNTorsion_one
#check psiSqDetectsNTorsion_two
#check psiSqDetectsNTorsion_three
#check prePsiFour_eval_eq_psiTwo_double
#check psiSqDetectsNTorsion_four
#print axioms n_torsion_finite_of_detector
#print axioms n_torsion_finite_of_psiSq_detection
#print axioms psiSqDetectsNTorsion_of_xFormula
#print axioms psiSq_two_eval_eq_negY_gap_sq
#print axioms divisionPolynomialXFormula_two
#print axioms psiSqDetectsNTorsion_of_xRelation
#print axioms divisionPolynomialXFormula_of_xRelation
#print axioms divisionPolynomialXRelation_zero
#print axioms divisionPolynomialXRelation_one
#print axioms divisionPolynomialXRelation_two
#print axioms divisionPolynomialXFormula_zero
#print axioms divisionPolynomialXFormula_one
#print axioms addX_mul_addNegX_kummer
#print axioms psiSqDetectsNTorsion_zero
#print axioms psiSqDetectsNTorsion_one
#print axioms psiSqDetectsNTorsion_two
#print axioms psiSqDetectsNTorsion_three
#print axioms prePsiFour_eval_eq_psiTwo_double
#print axioms psiSqDetectsNTorsion_four

end
end FLTMethodology.Torsion
