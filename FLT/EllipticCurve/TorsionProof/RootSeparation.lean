/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import FLT.EllipticCurve.TorsionProvider
public import FLT.EllipticCurve.TorsionProof.PsiSqExactDetection

/-!
# Root separation for prime-to-characteristic torsion

This file contains the generic polynomial and integral-root lemmas used to separate integral
torsion coordinates after reduction.  It deliberately has no dependency on the good-reduction
specialization construction.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- Two roots in a domain are equal if their images agree and the mapped polynomial is separable. -/
theorem roots_eq_of_same_map
    {A κ : Type*} [CommRing A] [IsDomain A] [Field κ]
    (ρ : A →+* κ) {p : A[X]} (hsep : (p.map ρ).Separable)
    {x y : A} (hx : p.IsRoot x) (hy : p.IsRoot y)
    (hbar : ρ x = ρ y) : x = y := by
  by_contra hxy
  let q := p /ₘ (X - C x)
  have hp : (X - C x) * q = p :=
    mul_divByMonic_eq_iff_isRoot.mpr hx
  have hqy : q.IsRoot y := by
    have heval := congrArg (fun f : A[X] ↦ f.eval y) hp
    have hprod : (y - x) * q.eval y = 0 := by
      simpa [Polynomial.IsRoot.def] using heval.trans hy
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (Ne.symm hxy))
  have hqmap : (X - C (ρ x)) ∣ q.map ρ := by
    rw [dvd_iff_isRoot, Polynomial.IsRoot.def, hbar, eval_map, eval₂_at_apply,
      hqy, map_zero]
  have hpmap : (X - C (ρ x)) * q.map ρ = p.map ρ := by
    simpa using congrArg (Polynomial.map ρ) hp
  have hsqdvd : (X - C (ρ x)) * (X - C (ρ x)) ∣ p.map ρ := by
    rw [← hpmap]
    exact mul_dvd_mul_left (X - C (ρ x)) hqmap
  exact Polynomial.not_isUnit_X_sub_C (ρ x) (hsep.squarefree _ hsqdvd)

/-- Roots of two pointwise-coprime separable factors remain distinct after reduction. -/
theorem roots_eq_of_two_separable_factors
    {A κ : Type*} [CommRing A] [IsDomain A] [Field κ]
    (ρ : A →+* κ) {p q : A[X]}
    (hpsep : (p.map ρ).Separable) (hqsep : (q.map ρ).Separable)
    (hcop : ∀ z : κ, (p.map ρ).eval z = 0 → (q.map ρ).eval z ≠ 0)
    {x y : A} (hx : p.IsRoot x ∨ q.IsRoot x)
    (hy : p.IsRoot y ∨ q.IsRoot y) (hbar : ρ x = ρ y) : x = y := by
  rcases hx with hpx | hqx <;> rcases hy with hpy | hqy
  · exact roots_eq_of_same_map ρ hpsep hpx hpy hbar
  · exfalso
    apply hcop (ρ x)
    · simpa [Polynomial.IsRoot.def, eval_map] using congrArg ρ hpx
    · rw [hbar]
      simpa [Polynomial.IsRoot.def, eval_map] using congrArg ρ hqy
  · exfalso
    apply hcop (ρ y)
    · simpa [Polynomial.IsRoot.def, eval_map] using congrArg ρ hpy
    · rw [← hbar]
      simpa [Polynomial.IsRoot.def, eval_map] using congrArg ρ hqx
  · exact roots_eq_of_same_map ρ hqsep hqx hqy hbar

/-- A root of a polynomial with unit leading coefficient over an integrally closed fraction ring
comes from the base ring. -/
theorem exists_lift_of_isRoot_of_isUnit_leadingCoeff
    {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    {p : A[X]} (hlc : IsUnit p.leadingCoeff) {x : K}
    (hx : (p.map (algebraMap A K)).IsRoot x) :
    ∃ a : A, algebraMap A K a = x := by
  let u : Aˣ := hlc.unit
  let q : A[X] := C ((u⁻¹ : Aˣ) : A) * p
  have hqmonic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    change ((u⁻¹ : Aˣ) : A) * p.leadingCoeff = 1
    rw [← hlc.unit_spec]
    exact Units.inv_mul u
  have hqroot : (q.map (algebraMap A K)).IsRoot x := by
    simp [q, Polynomial.IsRoot.def, hx.eq_zero]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨q, hqmonic, ?_⟩
  simpa [Polynomial.IsRoot.def, Polynomial.aeval_def, eval_map] using hqroot

end Polynomial

namespace WeierstrassCurve

/-- A root of `ΨSq n` is a root of `preΨ' n`, or (necessarily for even `n`) of `Ψ₂Sq`. -/
theorem prePsi_isRoot_or_even_and_psiTwoSq_isRoot_of_psiSq_isRoot
    {A : Type*} [CommRing A] [IsDomain A] (W : WeierstrassCurve A)
    {n : ℕ} {x : A} (hx : (W.ΨSq (n : ℤ)).IsRoot x) :
    (W.preΨ' n).IsRoot x ∨ Even n ∧ W.Ψ₂Sq.IsRoot x := by
  rw [Polynomial.IsRoot.def, W.ΨSq_ofNat, Polynomial.eval_mul,
    Polynomial.eval_pow] at hx
  by_cases heven : Even n
  · rw [if_pos heven] at hx
    rcases mul_eq_zero.mp hx with hpre | htwo
    · exact Or.inl (by simpa using hpre)
    · exact Or.inr ⟨heven, htwo⟩
  · rw [if_neg heven, Polynomial.eval_one, mul_one] at hx
    exact Or.inl (by simpa using hx)

/-- A root of the monic Weierstrass equation in `y` over an integrally closed fraction ring comes
from the base ring. -/
theorem exists_integral_y_of_equation
    {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    (W : WeierstrassCurve A) {x : A} {y : K}
    (hEq : (W.map (algebraMap A K)).toAffine.Equation
      (algebraMap A K x) y) :
    ∃ yA : A, algebraMap A K yA = y := by
  let p : A[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X +
    C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have hpmonic : p.Monic := by
    exact (isMonicOfDegree_add_add_two
      (W.a₁ * x + W.a₃)
      (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))).monic
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨p, hpmonic, ?_⟩
  rw [← Polynomial.aeval_def]
  rw [(W.map (algebraMap A K)).toAffine.equation_iff] at hEq
  simp only [p, Polynomial.aeval_def, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_add, map_mul, map_pow, map_neg]
  dsimp only [WeierstrassCurve.map] at hEq
  linear_combination hEq

/-- On an affine point of a Weierstrass curve, `Ψ₂Sq` is the square of the negation gap. -/
theorem psiTwoSq_eval_eq_negationGap_sq
    {F : Type*} [CommRing F] (W : WeierstrassCurve F)
    {x y : F} (hEq : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [W.toAffine.equation_iff] at hEq
  simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * hEq

end WeierstrassCurve
