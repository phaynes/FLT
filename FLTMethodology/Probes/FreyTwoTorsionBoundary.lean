/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.MazurSourceBoundary
import FLT.FreyCurve.Basic

/-!
# Full rational two-torsion on the Frey curve

This kernel-clean probe discharges the elementary Frey-curve input to the Mazur--Serre
irreducibility route.  It writes down the three nonzero rational points killed by two,
classifies every rational two-torsion point by factoring the transformed Frey equation, and
proves that the resulting four points are distinct.
-/

namespace FLTMethodology.Mazur

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

variable (P : FreyPackage)

-- Typeclass search does not unfold the redundant `Q`-to-`Q` base change automatically.
local instance freyCurveBaseChangeIsElliptic :
    WeierstrassCurve.IsElliptic (P.freyCurve⁄ℚ) := by
  change WeierstrassCurve.IsElliptic
    (P.freyCurve.map (algebraMap ℚ ℚ))
  infer_instance

private def xA : ℚ := (P.a : ℚ) ^ P.p / 4
private def yA : ℚ := -((P.a : ℚ) ^ P.p) / 8
private def xB : ℚ := -((P.b : ℚ) ^ P.p) / 4
private def yB : ℚ := (P.b : ℚ) ^ P.p / 8

private theorem equation_zero : P.freyCurve.toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [FreyPackage.freyCurve]

private theorem equation_A : P.freyCurve.toAffine.Equation (xA P) (yA P) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [FreyPackage.freyCurve, xA, yA]
  ring

private theorem equation_B : P.freyCurve.toAffine.Equation (xB P) (yB P) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [FreyPackage.freyCurve, xB, yB]
  ring

private def T0 : (P.freyCurve⁄ℚ).Point :=
  .some 0 0 (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_zero P))

private def TA : (P.freyCurve⁄ℚ).Point :=
  .some (xA P) (yA P) (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_A P))

private def TB : (P.freyCurve⁄ℚ).Point :=
  .some (xB P) (yB P) (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_B P))

private theorem T0_two : (2 : ℕ) • T0 P = 0 := by
  rw [two_nsmul]
  unfold T0
  apply Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, FreyPackage.freyCurve]

private theorem TA_two : (2 : ℕ) • TA P = 0 := by
  rw [two_nsmul]
  unfold TA
  apply Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, FreyPackage.freyCurve, xA, yA]
  ring

private theorem TB_two : (2 : ℕ) • TB P = 0 := by
  rw [two_nsmul]
  unfold TB
  apply Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, FreyPackage.freyCurve, xB, yB]
  ring

private theorem two_torsion_cases
    (Q : (P.freyCurve⁄ℚ).Point) (hQ : (2 : ℕ) • Q = 0) :
    Q = 0 ∨ Q = T0 P ∨ Q = TA P ∨ Q = TB P := by
  cases Q with
  | zero => exact Or.inl rfl
  | some x y hxy =>
      have hy : y = (P.freyCurve⁄ℚ).toAffine.negY x y := by
        by_contra hne
        have hadd := Point.add_self_of_Y_ne (h₁ := hxy) hne
        rw [two_nsmul, hadd] at hQ
        exact Point.some_ne_zero _ hQ
      have heq := hxy.1
      simp [WeierstrassCurve.Affine.negY, FreyPackage.freyCurve,
        WeierstrassCurve.baseChange, WeierstrassCurve.map] at hy
      rw [WeierstrassCurve.Affine.equation_iff] at heq
      simp [FreyPackage.freyCurve, WeierstrassCurve.baseChange,
        WeierstrassCurve.map] at heq
      have hfactor : x * (4 * x - (P.a : ℚ) ^ P.p) *
          (4 * x + (P.b : ℚ) ^ P.p) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with hleft | hxB
      · rcases mul_eq_zero.mp hleft with hxa | hxA
        · subst x
          have hy0 : y = 0 := by linarith
          subst y
          exact Or.inr (Or.inl (by simp [T0]))
        · have hx : x = xA P := by
            simp [xA] at hxA ⊢
            linarith
          have hy' : y = yA P := by
            rw [hx] at hy
            simp [xA, yA] at hy ⊢
            linarith
          subst x
          subst y
          exact Or.inr (Or.inr (Or.inl (by simp [TA])))
      · have hx : x = xB P := by
          simp [xB] at hxB ⊢
          linarith
        have hy' : y = yB P := by
          rw [hx] at hy
          simp [xB, yB] at hy ⊢
          linarith
        subst x
        subst y
        exact Or.inr (Or.inr (Or.inr (by simp [TB])))

private theorem T0_ne_zero : T0 P ≠ 0 := by
  unfold T0
  exact Point.some_ne_zero _

private theorem TA_ne_zero : TA P ≠ 0 := by
  unfold TA
  exact Point.some_ne_zero _

private theorem TB_ne_zero : TB P ≠ 0 := by
  unfold TB
  exact Point.some_ne_zero _

private theorem T0_ne_TA : T0 P ≠ TA P := by
  intro h
  have hx : (0 : ℚ) = xA P := (Point.some.inj h).1
  have haQ : ((P.a : ℚ) ^ P.p) ≠ 0 :=
    pow_ne_zero _ (Int.cast_ne_zero.mpr P.ha0)
  apply haQ
  simp [xA] at hx
  linarith

private theorem T0_ne_TB : T0 P ≠ TB P := by
  intro h
  have hx : (0 : ℚ) = xB P := (Point.some.inj h).1
  have hbQ : ((P.b : ℚ) ^ P.p) ≠ 0 :=
    pow_ne_zero _ (Int.cast_ne_zero.mpr P.hb0)
  apply hbQ
  simp [xB] at hx
  linarith

private theorem TA_ne_TB : TA P ≠ TB P := by
  intro h
  have hx : xA P = xB P := (Point.some.inj h).1
  have hsum : (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p = 0 := by
    simp [xA, xB] at hx
    linarith
  have hFLTQ : (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p = (P.c : ℚ) ^ P.p := by
    exact_mod_cast P.hFLT
  have hcQ : ((P.c : ℚ) ^ P.p) ≠ 0 :=
    pow_ne_zero _ (Int.cast_ne_zero.mpr P.hc0)
  exact hcQ (by linarith)

private theorem two_torsion_set :
    (AddSubgroup.torsionBy (P.freyCurve⁄ℚ).Point (2 : ℤ) :
      Set (P.freyCurve⁄ℚ).Point) = {0, T0 P, TA P, TB P} := by
  ext Q
  constructor
  · intro hQ
    have htwo : (2 : ℕ) • Q = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hQ
    rcases two_torsion_cases P Q htwo with h | h | h | h <;> simp [h]
  · intro hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rcases hQ with h | h | h | h
    · subst Q; simp
    · subst Q; exact T0_two P
    · subst Q; exact TA_two P
    · subst Q; exact TB_two P

/-- The Frey curve has all four of its two-torsion points over `Q`. -/
theorem freyCurve_hasFullRationalTwoTorsion :
    HasFullRationalTwoTorsion P.freyCurve := by
  rw [HasFullRationalTwoTorsion, two_torsion_set]
  have hzero : (0 : (P.freyCurve⁄ℚ).Point) ∉
      ({T0 P, TA P, TB P} : Set (P.freyCurve⁄ℚ).Point) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(T0_ne_zero P).symm, (TA_ne_zero P).symm, (TB_ne_zero P).symm⟩
  rw [Set.ncard_insert_of_notMem hzero]
  have hT0 : T0 P ∉ ({TA P, TB P} : Set (P.freyCurve⁄ℚ).Point) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨T0_ne_TA P, T0_ne_TB P⟩
  rw [Set.ncard_insert_of_notMem hT0, Set.ncard_pair (TA_ne_TB P)]

#check freyCurve_hasFullRationalTwoTorsion
#print axioms freyCurve_hasFullRationalTwoTorsion

end
end FLTMethodology.Mazur
