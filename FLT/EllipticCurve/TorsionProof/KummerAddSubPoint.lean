/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.PrePsiWindowSteps
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- Coordinate-free equality in projective two-space. Nonzeroness is tracked separately. -/
def ProjectivelyEquivalent3 (u v : Fin 3 → k) : Prop :=
  ∀ i j, u i * v j = u j * v i

@[refl] theorem ProjectivelyEquivalent3.refl (u : Fin 3 → k) :
    ProjectivelyEquivalent3 u u := by
  intro i j
  exact mul_comm _ _

theorem ProjectivelyEquivalent3.symm {u v : Fin 3 → k}
    (h : ProjectivelyEquivalent3 u v) : ProjectivelyEquivalent3 v u := by
  intro i j
  simpa [mul_comm] using h j i

theorem addX_add_addNegX_kummerMiddle
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x₁ x₂ y₁ y₂ : k} (h₁ : E.toAffine.Nonsingular x₁ y₁)
    (h₂ : E.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    let xplus := E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)
    let xminus := E.toAffine.addX x₁ x₂
      (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))
    (xplus + xminus) * (x₁ - x₂) ^ 2 =
      kummerBiquadraticMiddleHomogeneous E x₁ 1 x₂ 1 := by
  dsimp only [kummerBiquadraticMiddleHomogeneous]
  rw [E.toAffine.slope_of_X_ne hx]
  rw [E.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  field_simp [sub_ne_zero.mpr hx]
  have heq₁ := h₁.1
  have heq₂ := h₂.1
  rw [E.toAffine.equation_iff] at heq₁ heq₂
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 2 * heq₁ + 2 * heq₂

theorem addSubMap_eval_sym2x_affine
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x₁ x₂ y₁ y₂ : k} (h₁ : (E⁄k).Nonsingular x₁ y₁)
    (h₂ : (E⁄k).Nonsingular x₂ y₂) :
    (fun i ↦ (E.addSubMap i).eval
      ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point).sym2x
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : (E⁄k).Point))) =
      ![kummerBiquadratic E x₁ x₂,
        kummerBiquadraticMiddleHomogeneous E x₁ 1 x₂ 1,
        (x₁ - x₂) ^ 2] := by
  rw [WeierstrassCurve.Affine.Point.sym2x_some_some]
  funext i
  fin_cases i <;>
    simp [WeierstrassCurve.addSubMap, kummerBiquadratic,
      kummerBiquadraticMiddleHomogeneous] <;>
    ring

theorem addSubMap_sym2x_distinct
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x₁ x₂ y₁ y₂ : k} (h₁ : (E⁄k).Nonsingular x₁ y₁)
    (h₂ : (E⁄k).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x₁ y₁ h₁
    let Q : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x₂ y₂ h₂
    (fun i ↦ (E.addSubMap i).eval (P.sym2x Q)) =
      fun i ↦ (x₁ - x₂) ^ 2 * ((P + Q).sym2x (P - Q) i) := by
  have h₁E : E.toAffine.Nonsingular x₁ y₁ := by
    change E.toAffine.Nonsingular x₁ y₁ at h₁
    exact h₁
  have h₂E : E.toAffine.Nonsingular x₂ y₂ := by
    change E.toAffine.Nonsingular x₂ y₂ at h₂
    exact h₂
  have hslope (xa xb ya yb : k) :
      (E⁄k).slope xa xb ya yb = E.toAffine.slope xa xb ya yb := by
    simp [WeierstrassCurve.Affine.slope]
  dsimp only
  rw [addSubMap_eval_sym2x_affine E h₁ h₂]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp_rw [hslope]
  simp only [WeierstrassCurve.Affine.Point.sym2x_some_some]
  funext i
  fin_cases i
  · simp
    simpa [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      sub_eq_add_neg, mul_comm] using
        (addX_mul_addNegX_kummer E h₁E h₂E hx).symm
  · simp
    simpa [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      sub_eq_add_neg, mul_comm] using
        (addX_add_addNegX_kummerMiddle E h₁E h₂E hx).symm
  · simp

theorem projectivelyEquivalent3_scale (c : k) (v : Fin 3 → k) :
    ProjectivelyEquivalent3 (fun i ↦ c * v i) v := by
  intro i j
  ring

theorem projectivelyEquivalent3_affine {X Z x : k} (h : x * Z = X) :
    ProjectivelyEquivalent3 ![X, Z, 0] ![x, 1, 0] := by
  subst X
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem projectivelyEquivalent3_infinity {X Z : k} (h : Z = 0) :
    ProjectivelyEquivalent3 ![X, Z, 0] ![1, 0, 0] := by
  subst Z
  intro i j
  fin_cases i <;> fin_cases j <;> simp

theorem addSubMap_eval_sym2x_self
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : (E⁄k).Nonsingular x y) :
    (fun i ↦ (E.addSubMap i).eval
      ((WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point).sym2x
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point))) =
      ![(E.Φ 2).eval x, (E.ΨSq 2).eval x, 0] := by
  rw [addSubMap_eval_sym2x_affine E h h]
  funext i
  fin_cases i
  · simp
    simp only [kummerBiquadratic]
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp
    simp only [kummerBiquadraticMiddleHomogeneous,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · simp

theorem addSubMap_sym2x_self_projective
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {x y : k} (h : (E⁄k).Nonsingular x y) :
    let P : (E⁄k).Point := WeierstrassCurve.Affine.Point.some x y h
    ProjectivelyEquivalent3
      (fun i ↦ (E.addSubMap i).eval (P.sym2x P))
      ((P + P).sym2x (P - P)) := by
  have hE : E.toAffine.Nonsingular x y := by
    change E.toAffine.Nonsingular x y at h
    exact h
  dsimp only
  rw [addSubMap_eval_sym2x_self E h]
  rw [sub_self]
  have hrel := divisionPolynomialXRelation_two E hE
  change
    match
      (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point)
    with
    | .zero => (E.ΨSq (2 : ℤ)).eval x = 0
    | .some xn _ _ => xn * (E.ΨSq (2 : ℤ)).eval x = (E.Φ (2 : ℤ)).eval x at hrel
  generalize hdouble :
      (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) +
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = Q at hrel ⊢
  cases Q with
  | zero =>
      rw [← WeierstrassCurve.Affine.Point.zero_def]
      rw [WeierstrassCurve.Affine.Point.sym2x_zero_zero]
      exact projectivelyEquivalent3_infinity hrel
  | some x₂ y₂ h₂ =>
      rw [WeierstrassCurve.Affine.Point.sym2x_some_zero]
      exact projectivelyEquivalent3_affine hrel

theorem addSubMap_sym2x_zero_exact
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    (Q : (E⁄k).Point) :
    (fun i ↦ (E.addSubMap i).eval ((0 : (E⁄k).Point).sym2x Q)) =
      Q.sym2x (-Q) := by
  rcases Q with (_ | ⟨x, y, h⟩)
  · change (fun i ↦ (E.addSubMap i).eval
        ((0 : (E⁄k).Point).sym2x (0 : (E⁄k).Point))) =
        (0 : (E⁄k).Point).sym2x (0 : (E⁄k).Point)
    funext i
    fin_cases i <;>
      simp [WeierstrassCurve.addSubMap]
  · funext i
    fin_cases i <;>
      simp [WeierstrassCurve.addSubMap] <;> ring

theorem addSubMap_sym2x_zero_right_exact
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    (P : (E⁄k).Point) :
    (fun i ↦ (E.addSubMap i).eval (P.sym2x (0 : (E⁄k).Point))) =
      P.sym2x P := by
  rw [WeierstrassCurve.Affine.Point.sym2x_comm]
  rw [addSubMap_sym2x_zero_exact E P]
  exact WeierstrassCurve.Affine.Point.sym2x_neg_right P P

/-- Mathlib's add-and-sub map has the advertised projective action on every pair of affine
points, including infinity, doubling, and two-torsion degeneracies. -/
theorem addSubMap_sym2x_projective
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    (P Q : (E⁄k).Point) :
    ProjectivelyEquivalent3
      (fun i ↦ (E.addSubMap i).eval (P.sym2x Q))
      ((P + Q).sym2x (P - Q)) := by
  by_cases hP : P = 0
  · subst P
    rw [addSubMap_sym2x_zero_exact E Q]
    exact ProjectivelyEquivalent3.refl (k := k) _
  by_cases hQ : Q = 0
  · subst Q
    rw [addSubMap_sym2x_zero_right_exact E P]
    simpa only [add_zero, sub_zero] using
      (ProjectivelyEquivalent3.refl (k := k) (P.sym2x P))
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · exact (hP rfl).elim
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · exact (hQ rfl).elim
  by_cases hx : x₁ = x₂
  · subst x₂
    have hpq :
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) =
            WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ ∨
          (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) =
            -(WeierstrassCurve.Affine.Point.some x₁ y₂ h₂) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff (W := E⁄k)).mp rfl
    rcases hpq with hpq | hpq
    · cases hpq
      exact addSubMap_sym2x_self_projective E h₁
    · have hqp :
          (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ : (E⁄k).Point) =
            -(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := by
        calc
          _ = -(-(WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ : (E⁄k).Point)) :=
            (neg_neg _).symm
          _ = _ := congrArg Neg.neg hpq.symm
      rw [hqp]
      have hself := addSubMap_sym2x_self_projective E h₁
      rw [WeierstrassCurve.Affine.Point.sym2x_neg_right]
      simp only [add_neg_cancel, sub_neg_eq_add]
      rw [WeierstrassCurve.Affine.Point.sym2x_comm
        (0 : (E⁄k).Point)
        ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) +
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)]
      simpa only [sub_self] using hself
  · have heq := addSubMap_sym2x_distinct E h₁ h₂ hx
    rw [heq]
    exact projectivelyEquivalent3_scale _ _

end

end FLTMethodology.Torsion
