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

theorem n_torsion_finite_of_psiSq_detection
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    Finite (E.nTorsion n) :=
  n_torsion_finite_of_detector E (psiSqTorsionXDetector E hn hdetect)

#check n_torsion_finite_of_detector
#check n_torsion_finite_of_psiSq_detection
#check psiSqDetectsNTorsion_two
#check psiSqDetectsNTorsion_three
#print axioms n_torsion_finite_of_detector
#print axioms n_torsion_finite_of_psiSq_detection
#print axioms psiSqDetectsNTorsion_two
#print axioms psiSqDetectsNTorsion_three

end
end FLTMethodology.Torsion
