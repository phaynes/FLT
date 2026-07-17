/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.PsiSqExactDetection
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Cardinality assembly for elliptic-curve torsion

This module turns exact division-polynomial detection into a cardinality boundary. It identifies
`E[n]` with infinity plus the affine zero locus cut out by `PsiSq_n` and the Weierstrass equation.
Consequently an affine zero-locus count of `n^2 - 1` implies the frozen `n^2` torsion-cardinality
statement. The remaining obligation is the separability, multiplicity, and y-fibre count itself.
-/

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

variable {k : Type u} [Field k]

def psiSqAffineZeroSet
    (E : WeierstrassCurve k) (n : ℕ) : Set (k × k) :=
  {xy | (E.ΨSq (n : ℤ)).eval xy.1 = 0 ∧ E.toAffine.Equation xy.1 xy.2}

def affineTorsionCoordinateSet
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Set (k × k) :=
  {xy | ∃ h : E.toAffine.Nonsingular xy.1 xy.2,
    WeierstrassCurve.Affine.Point.some xy.1 xy.2 h ∈
      Submodule.torsionBy ℤ (E⁄k).Point n}

def affineTorsionCoordinatesEquivPsiSqZero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    affineTorsionCoordinateSet E n ≃ psiSqAffineZeroSet E n :=
  Equiv.subtypeEquiv (Equiv.refl (k × k)) <| by
    intro xy
    change (∃ h : E.toAffine.Nonsingular xy.1 xy.2,
      (WeierstrassCurve.Affine.Point.some xy.1 xy.2 h : (E⁄k).Point) ∈
        Submodule.torsionBy ℤ (E⁄k).Point n) ↔
      ((E.ΨSq (n : ℤ)).eval xy.1 = 0 ∧
        E.toAffine.Equation xy.1 xy.2)
    rcases xy with ⟨x, y⟩
    constructor
    · rintro ⟨h, htorsion⟩
      refine ⟨?_, E.toAffine.equation_iff_nonsingular.mpr h⟩
      apply (psiSq_eval_eq_zero_iff_nsmul_eq_zero E h).2
      exact (Submodule.mem_torsionBy_iff _ _).mp htorsion
    · rintro ⟨hpsi, heq⟩
      let h : E.toAffine.Nonsingular x y :=
        E.toAffine.equation_iff_nonsingular.mp heq
      have ht : (n : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y h : (E⁄k).Point) = 0
        := (psiSq_eval_eq_zero_iff_nsmul_eq_zero E h).1 hpsi
      exact ⟨h, (Submodule.mem_torsionBy_iff _ _).2 ht⟩

def nTorsionEquivWithZeroPsiSqZero
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    E.nTorsion n ≃ WithZero (psiSqAffineZeroSet E n) := by
  change (Submodule.torsionBy ℤ (E⁄k).Point n) ≃
    Option (psiSqAffineZeroSet E n)
  let e := WeierstrassCurve.Affine.nonsingularPointEquivSubtype
    (W' := E.toAffine)
    (p := fun P ↦ P ∈ Submodule.torsionBy ℤ (E⁄k).Point n)
    (show (0 : (E⁄k).Point) ∈ Submodule.torsionBy ℤ (E⁄k).Point n by simp)
  exact e.trans (affineTorsionCoordinatesEquivPsiSqZero E n).optionCongr

/-- The exact remaining zero-locus count after the point/division-polynomial dictionary has been
closed. Its proof must account for root multiplicities and the one- versus two-point y-fibres. -/
def PsiSqAffineZeroCard
    (E : WeierstrassCurve k) (n : ℕ) : Prop :=
  Nat.card (psiSqAffineZeroSet E n) = n ^ 2 - 1

theorem n_torsion_card_of_psiSq_affine_zero_card
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : 0 < n)
    (hcard : PsiSqAffineZeroCard E n) :
    Nat.card (E.nTorsion n) = n ^ 2 := by
  have hfinite : (psiSqAffineZeroSet E n).Finite := by
    simpa only [psiSqAffineZeroSet, detectedAffineSet] using
      detectedAffineSet_finite E (E.ΨSq (n : ℤ))
        (psiSq_ne_zero_all_characteristics E hn)
  letI : Finite (psiSqAffineZeroSet E n) := hfinite
  rw [Nat.card_congr (nTorsionEquivWithZeroPsiSqZero E n)]
  change Nat.card (Option (psiSqAffineZeroSet E n)) = n ^ 2
  rw [Finite.card_option, show Nat.card (psiSqAffineZeroSet E n) = n ^ 2 - 1 from hcard]
  have hsq : 0 < n ^ 2 := pow_pos hn 2
  omega

end

end FLTMethodology.Torsion
