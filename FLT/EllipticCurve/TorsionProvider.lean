/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.EllipticCurve.TorsionDefs
public import FLT.EllipticCurve.TorsionProof.PrePsiSeparableOfTorsionCard
public import HasseWeil.HasseBound.WeilPairing.TorsionCardEll

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

noncomputable section

universe u

namespace FLT.EllipticCurve.TorsionProvider

variable {k : Type u} [Field k]

theorem nTorsion_finite
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) :=
  FLTMethodology.Torsion.n_torsion_finite_all_characteristics E hn

def nTorsionEquivAintlibTorsion
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) :
    E.nTorsion n ≃ HasseWeil.torsionSubgroup E.toAffine (n : ℤ) :=
  Equiv.subtypeEquiv (Equiv.refl E.toAffine.Point) <| by
    intro P
    rw [Submodule.mem_torsionBy_iff, HasseWeil.mem_torsionSubgroup]
    rfl

theorem nTorsion_card_algClosed
    [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n ^ 2 := by
  rw [Nat.card_congr (nTorsionEquivAintlibTorsion E n)]
  have hnZ : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hn
  have h := HasseWeil.WeilPairing.TorsionGeometric.card_torsion_ell E (n : ℤ) hnZ
  exact_mod_cast h

theorem prePsi_separable
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (E.preΨ' n).Separable := by
  letI : DecidableEq (AlgebraicClosure k) := Classical.decEq _
  rw [← Polynomial.separable_map (algebraMap k (AlgebraicClosure k))]
  rw [← WeierstrassCurve.map_preΨ']
  have hn' : (n : AlgebraicClosure k) ≠ 0 :=
    (map_ne_zero (algebraMap k (AlgebraicClosure k))).2 hn
  exact FLTMethodology.Torsion.prePsi_separable_of_n_torsion_card
    (E.map (algebraMap k (AlgebraicClosure k))) hn'
    (nTorsion_card_algClosed (E.map (algebraMap k (AlgebraicClosure k))) hn')

theorem nTorsion_card_sepClosed
    [IsSepClosed k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n ^ 2 :=
  FLTMethodology.Torsion.n_torsion_card_of_prePsi_separable E hn
    (prePsi_separable E hn)

#print axioms nTorsion_finite
#print axioms nTorsion_card_sepClosed

end FLT.EllipticCurve.TorsionProvider
