/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.DualTangent
import FLT.EllipticCurve.TorsionProof.PrePsiTwoTorsion

/-!
# Repeated division-polynomial roots as infinitesimal kernel witnesses

This module assembles the local algebra around the final `preΨ'` separability obligation.  Over a
separably closed field, a hypothetical common root of `preΨ' n` and its derivative is first lifted
to an affine point on the elliptic curve.  The already-proved coprimality with `Ψ₂Sq` makes the
`Y` partial nonzero, so the point has a canonical nonconstant lift to dual numbers.  Both the
mapped curve equation and the mapped division polynomial vanish at that lift.

Consequently the remaining proof cannot be hidden in root counting: it must rule out this explicit
infinitesimal kernel witness.  The standard mathematical discharge is that the differential of
multiplication by `n` is scalar multiplication by `n`, hence injective when `(n : k) ≠ 0`.
-/

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- The concrete data produced by a hypothetical repeated root of `preΨ' n`. -/
structure PrePsiInfinitesimalWitness
    (E : WeierstrassCurve k) (n : ℕ) (x : k) where
  /-- An affine `y`-coordinate over the supplied `x`-coordinate. -/
  y : k
  baseEquation : E.toAffine.Equation x y
  yPartial_ne : E.toAffine.polynomialY.evalEval x y ≠ 0
  dualEquation :
    ((E.map (algebraMap k (DualNumber k))).toAffine.Equation
      (dualPoint x 1) (dualPoint y (dualTangentY E x y 1)))
  dualPrePsiZero :
    ((E.map (algebraMap k (DualNumber k))).preΨ' n).eval (dualPoint x 1) = 0

/-- A common root of `preΨ' n` and its derivative yields a nonconstant dual-number point on the
curve at which the mapped division polynomial still vanishes. -/
def prePsiInfinitesimalWitness_of_commonRoot
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k}
    (hroot : (E.preΨ' n).eval x = 0)
    (hderiv : (E.preΨ' n).derivative.eval x = 0) :
    PrePsiInfinitesimalWitness E n x := by
  have htwo : E.Ψ₂Sq.eval x ≠ 0 := prePsi_pointwise_coprime E hn x hroot
  have hfiberSep : (fiberPolynomial E x).Separable :=
    fiberPolynomial_separable_of_psiTwoSq_eval_ne_zero E x htwo
  have hcard : Nat.card (curveYFiber E x) = 2 :=
    curveYFiber_card_eq_two_of_separable E x hfiberSep
  letI : Finite (curveYFiber E x) := curveYFiber_finite E x
  have hnonempty : Nonempty (curveYFiber E x) := by
    apply Finite.card_pos_iff.mp
    omega
  let yy : curveYFiber E x := Classical.choice hnonempty
  let y : k := yy.1
  have hy : E.toAffine.Equation x y := yy.2
  have hEquation : E.toAffine.Equation x y := hy
  have hYPartial : E.toAffine.polynomialY.evalEval x y ≠ 0 := by
    intro hzero
    apply htwo
    rw [← polynomialY_sq_eq_psiTwoSq_of_equation E hEquation, hzero]
    simp
  exact
    { y := y
      baseEquation := hEquation
      yPartial_ne := hYPartial
      dualEquation := dualTangentY_equation E hEquation hYPartial 1
      dualPrePsiZero := prePsi_commonRoot_gives_dual_zero E n hroot hderiv }

/-- A separability proof now reduces to excluding the explicit witness above.  This theorem is a
logical assembly lemma: the substantive remaining input is `hNoWitness`, which should be discharged
from the differential of multiplication by `n`, not assumed at the provider boundary. -/
theorem prePsi_separable_of_no_infinitesimalWitness
    [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    (hNoWitness : ∀ x : k, IsEmpty (PrePsiInfinitesimalWitness E n x)) :
    (E.preΨ' n).Separable := by
  rw [Polynomial.separable_def]
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k]
  intro x
  by_contra h
  push Not at h
  have hpre : (E.preΨ' n).eval x = 0 := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using h.1
  have hderiv : (E.preΨ' n).derivative.eval x = 0 := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using h.2
  exact (hNoWitness x).false
    (prePsiInfinitesimalWitness_of_commonRoot E hn hpre hderiv)

end

end FLTMethodology.Torsion
