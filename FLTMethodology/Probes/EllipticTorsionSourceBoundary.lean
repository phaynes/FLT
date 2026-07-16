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

theorem n_torsion_finite_of_psiSq_detection
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    Finite (E.nTorsion n) :=
  n_torsion_finite_of_detector E (psiSqTorsionXDetector E hn hdetect)

#check n_torsion_finite_of_detector
#check n_torsion_finite_of_psiSq_detection
#print axioms n_torsion_finite_of_detector
#print axioms n_torsion_finite_of_psiSq_detection

end
end FLTMethodology.Torsion
