/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.TorsionCardAssembly
import Mathlib.Data.Fintype.BigOperators

/-!
# Fibre decomposition of the division-polynomial zero locus

The affine zero locus used by the torsion-cardinality assembly is equivalent to a dependent sum:
for each x-root of `PsiSq_n`, take the y-coordinates satisfying the Weierstrass equation. This
module proves the equivalence, finiteness of both indexing roots and fibres, the resulting
finite-sum cardinality formula, and a uniform-fibre specialization.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine BigOperators

noncomputable section

universe u

variable {k : Type u} [Field k]

def polynomialZeroSet (f : k[X]) : Set k :=
  {x | f.eval x = 0}

def curveYFiber (E : WeierstrassCurve k) (x : k) : Set k :=
  {y | E.toAffine.Equation x y}

def psiSqAffineZeroEquivSigma
    (E : WeierstrassCurve k) (n : ℕ) :
    psiSqAffineZeroSet E n ≃
      Σ x : polynomialZeroSet (E.ΨSq (n : ℤ)), curveYFiber E x :=
  { toFun := fun xy ↦ ⟨⟨xy.1.1, xy.2.1⟩, ⟨xy.1.2, xy.2.2⟩⟩
    invFun := fun xy ↦ ⟨(xy.1.1, xy.2.1), xy.1.2, xy.2.2⟩
    left_inv := fun xy ↦ by ext <;> rfl
    right_inv := fun xy ↦ by ext <;> rfl }

def psiSqAffineZeroEquivRootSigma
    (E : WeierstrassCurve k) (n : ℕ) (hpsi : E.ΨSq (n : ℤ) ≠ 0) :
    psiSqAffineZeroSet E n ≃
      Σ x : (E.ΨSq (n : ℤ)).rootSet k, curveYFiber E x :=
  { toFun := fun xy ↦
      ⟨⟨xy.1.1, (Polynomial.mem_rootSet_of_ne hpsi).2 xy.2.1⟩,
        ⟨xy.1.2, xy.2.2⟩⟩
    invFun := fun xy ↦
      ⟨(xy.1.1, xy.2.1), (Polynomial.mem_rootSet_of_ne hpsi).1 xy.1.2, xy.2.2⟩
    left_inv := fun xy ↦ by ext <;> rfl
    right_inv := fun xy ↦ by ext <;> rfl }

theorem polynomialZeroSet_finite {f : k[X]} (hf : f ≠ 0) :
    Finite (polynomialZeroSet f) := by
  let e : polynomialZeroSet f ≃ f.rootSet k :=
    Equiv.subtypeEquiv (Equiv.refl k) <| by
      intro x
      simp only [polynomialZeroSet, Set.mem_setOf_eq, Equiv.refl_apply]
      exact (Polynomial.mem_rootSet_of_ne hf).symm
  exact Finite.of_equiv (f.rootSet k) e.symm

theorem curveYFiber_finite (E : WeierstrassCurve k) (x : k) :
    Finite (curveYFiber E x) := by
  let e : curveYFiber E x ≃ (fiberPolynomial E x).rootSet k :=
    Equiv.subtypeEquiv (Equiv.refl k) <| by
      intro y
      simp only [curveYFiber, Set.mem_setOf_eq, Equiv.refl_apply]
      rw [equation_iff_eval_fiberPolynomial]
      exact (Polynomial.mem_rootSet_of_ne (fiberPolynomial_ne_zero E x)).symm
  exact Finite.of_equiv ((fiberPolynomial E x).rootSet k) e.symm

theorem psiSqAffineZeroCard_eq_sum_yFibers
    (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : 0 < n) :
    Nat.card (psiSqAffineZeroSet E n) =
      ∑ x : (E.ΨSq (n : ℤ)).rootSet k, Nat.card (curveYFiber E x) := by
  letI (x : (E.ΨSq (n : ℤ)).rootSet k) : Finite (curveYFiber E x) :=
    curveYFiber_finite E x
  rw [Nat.card_congr (psiSqAffineZeroEquivRootSigma E n
    (psiSq_ne_zero_all_characteristics E hn)), Nat.card_sigma]

theorem psiSqAffineZeroCard_of_uniform_yFiber
    (E : WeierstrassCurve k) [E.IsElliptic]
    {n c r : ℕ} (hn : 0 < n)
    (hfiber : ∀ x : (E.ΨSq (n : ℤ)).rootSet k,
      Nat.card (curveYFiber E x) = c)
    (hroots : Fintype.card ((E.ΨSq (n : ℤ)).rootSet k) = r) :
    Nat.card (psiSqAffineZeroSet E n) = r * c := by
  rw [psiSqAffineZeroCard_eq_sum_yFibers E hn]
  calc
    (∑ x : (E.ΨSq (n : ℤ)).rootSet k, Nat.card (curveYFiber E x)) =
        ∑ _x : (E.ΨSq (n : ℤ)).rootSet k, c := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact hfiber x
    _ = Fintype.card ((E.ΨSq (n : ℤ)).rootSet k) * c := by simp
    _ = r * c := by rw [hroots]

end

end FLTMethodology.Torsion
