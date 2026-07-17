/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# Dual-number tangents for the division-polynomial separability boundary

This module supplies the first-order algebra needed by the remaining elliptic-torsion source
obligation.  Polynomial evaluation at `x + ε dx` splits into its value and formal derivative, and
the same representation turns the Weierstrass equation into its base equation plus the usual
tangent equation.  A common root of `preΨ' n` and its derivative therefore gives a genuine
nonconstant dual-number zero of the mapped division polynomial.

The module deliberately stops before claiming that this dual zero is killed by multiplication by
`n`.  That is the remaining group-law/differential bridge; keeping it explicit prevents the local
polynomial calculation from being mistaken for the global separability theorem.
-/

namespace FLTMethodology.Torsion

open Polynomial
open TrivSqZeroExt
open WeierstrassCurve

noncomputable section

universe u

variable {k : Type u} [CommRing k]

/-- The dual number `x + ε dx`. -/
def dualPoint (x dx : k) : DualNumber k :=
  inl x + inr dx

@[simp] theorem dualPoint_fst (x dx : k) : (dualPoint x dx).fst = x := by
  simp [dualPoint]

@[simp] theorem dualPoint_snd (x dx : k) : (dualPoint x dx).snd = dx := by
  simp [dualPoint]

theorem polynomial_eval₂_dualPoint_fst (p : k[X]) (x dx : k) :
    (p.eval₂ (algebraMap k (DualNumber k)) (dualPoint x dx)).fst = p.eval x := by
  change (TrivSqZeroExt.fstHom k k k).toRingHom
      (p.eval₂ (algebraMap k (DualNumber k)) (dualPoint x dx)) = p.eval x
  rw [Polynomial.hom_eval₂ p (algebraMap k (DualNumber k))
    (TrivSqZeroExt.fstHom k k k).toRingHom (dualPoint x dx)]
  simp [dualPoint]

theorem polynomial_eval₂_dualPoint_snd (p : k[X]) (x dx : k) :
    (p.eval₂ (algebraMap k (DualNumber k)) (dualPoint x dx)).snd =
      p.derivative.eval x * dx := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.derivative_eval,
    Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
  simp only [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, dualPoint_fst, dualPoint_snd,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [nsmul_eq_mul, smul_eq_mul, smul_zero, add_zero, Nat.pred_eq_sub_one]
  ring

/-- Exact first-order Taylor expansion for a univariate polynomial over dual numbers. -/
theorem polynomial_eval₂_dualPoint (p : k[X]) (x dx : k) :
    p.eval₂ (algebraMap k (DualNumber k)) (dualPoint x dx) =
      inl (p.eval x) + inr (p.derivative.eval x * dx) := by
  ext
  · simp [polynomial_eval₂_dualPoint_fst]
  · simp [polynomial_eval₂_dualPoint_snd]

/-- The residual of the mapped Weierstrass equation over dual numbers consists of the ordinary
residual and the linear tangent residual. -/
theorem weierstrassResidual_dualPoint
    (E : WeierstrassCurve k) (x dx y dy : k) :
    let f := algebraMap k (DualNumber k)
    let ED := (E.map f).toAffine
    let A := E.toAffine
    (dualPoint y dy) ^ 2 + ED.a₁ * dualPoint x dx * dualPoint y dy +
        ED.a₃ * dualPoint y dy -
          ((dualPoint x dx) ^ 3 + ED.a₂ * (dualPoint x dx) ^ 2 +
            ED.a₄ * dualPoint x dx + ED.a₆) =
      dualPoint
        (y ^ 2 + A.a₁ * x * y + A.a₃ * y -
          (x ^ 3 + A.a₂ * x ^ 2 + A.a₄ * x + A.a₆))
        (A.polynomialX.evalEval x y * dx + A.polynomialY.evalEval x y * dy) := by
  dsimp only
  ext
  · simp [dualPoint, WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY,
      TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualPoint, WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY,
      TrivSqZeroExt.algebraMap_eq_inl]
    ring

/-- A dual-number point lies on the mapped curve exactly when its base point lies on the original
curve and its infinitesimal coordinates satisfy the tangent equation. -/
theorem dualEquation_iff
    (E : WeierstrassCurve k) (x dx y dy : k) :
    ((E.map (algebraMap k (DualNumber k))).toAffine.Equation
      (dualPoint x dx) (dualPoint y dy)) ↔
      (E.toAffine.Equation x y ∧
        E.toAffine.polynomialX.evalEval x y * dx +
          E.toAffine.polynomialY.evalEval x y * dy = 0) := by
  rw [WeierstrassCurve.Affine.equation_iff',
    weierstrassResidual_dualPoint,
    WeierstrassCurve.Affine.equation_iff']
  constructor
  · intro h
    constructor
    · have := congrArg TrivSqZeroExt.fst h
      simpa [dualPoint] using this
    · have := congrArg TrivSqZeroExt.snd h
      simpa [dualPoint] using this
  · rintro ⟨hx, ht⟩
    apply TrivSqZeroExt.ext
    · simpa [dualPoint] using hx
    · simpa [dualPoint] using ht

/-- On the curve, the square of the `Y` partial is the two-division polynomial. -/
theorem polynomialY_sq_eq_psiTwoSq_of_equation
    (E : WeierstrassCurve k) {x y : k} (hxy : E.toAffine.Equation x y) :
    E.toAffine.polynomialY.evalEval x y ^ 2 = E.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  rw [WeierstrassCurve.Affine.equation_iff] at hxy
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  linear_combination 4 * hxy

/-- The unique `y`-direction completing a chosen `x`-direction when the `Y` partial is nonzero. -/
noncomputable def dualTangentY {F : Type*} [Field F]
    (E : WeierstrassCurve F) (x y dx : F) : F :=
  -(E.toAffine.polynomialX.evalEval x y * dx) /
    E.toAffine.polynomialY.evalEval x y

theorem dualTangentY_spec
    {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : F}
    (hy : E.toAffine.polynomialY.evalEval x y ≠ 0) (dx : F) :
    E.toAffine.polynomialX.evalEval x y * dx +
        E.toAffine.polynomialY.evalEval x y * dualTangentY E x y dx = 0 := by
  rw [dualTangentY]
  field_simp
  ring

theorem dualTangentY_equation
    {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : F}
    (hxy : E.toAffine.Equation x y)
    (hy : E.toAffine.polynomialY.evalEval x y ≠ 0) (dx : F) :
    ((E.map (algebraMap F (DualNumber F))).toAffine.Equation
      (dualPoint x dx) (dualPoint y (dualTangentY E x y dx))) := by
  exact (dualEquation_iff E x dx y (dualTangentY E x y dx)).2
    ⟨hxy, dualTangentY_spec E hy dx⟩

/-- Mapping a division polynomial to dual numbers exposes its value and derivative. -/
theorem prePsi_map_eval_dualPoint
    (E : WeierstrassCurve k) (n : ℕ) (x dx : k) :
    ((E.map (algebraMap k (DualNumber k))).preΨ' n).eval (dualPoint x dx) =
      dualPoint ((E.preΨ' n).eval x) ((E.preΨ' n).derivative.eval x * dx) := by
  rw [WeierstrassCurve.map_preΨ', Polynomial.eval_map]
  exact polynomial_eval₂_dualPoint (E.preΨ' n) x dx

/-- A repeated root of `preΨ' n` produces a nonconstant dual-number zero of its base change. -/
theorem prePsi_commonRoot_gives_dual_zero
    (E : WeierstrassCurve k) (n : ℕ) {x : k}
    (hroot : (E.preΨ' n).eval x = 0)
    (hderiv : (E.preΨ' n).derivative.eval x = 0) :
    ((E.map (algebraMap k (DualNumber k))).preΨ' n).eval (dualPoint x 1) = 0 := by
  rw [prePsi_map_eval_dualPoint, hroot, hderiv]
  simp [dualPoint]

end

end FLTMethodology.Torsion
