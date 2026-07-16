/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.MazurSourceBoundary
import FLT.EllipticCurve.Torsion

/-!
# Kernel-clean assembly boundary for the Mazur--Serre torsion contradiction

This file separates the genuinely deep character and quotient-isogeny providers from the final
group-theoretic and cardinality argument. Full rational two-torsion and an embedded rational
`p`-torsion line give `4*p` distinct torsion points. The terminal irreducibility assembly is stated
over an abstract Galois representation so it does not inherit admissions from the current concrete
elliptic-curve torsion representation constructor.
-/

namespace FLTMethodology.Mazur

open scoped WeierstrassCurve.Affine

noncomputable section

variable {G : Type*} [AddCommGroup G] (p : ℕ) [Fact p.Prime]

private def torsionPairMap (f : ZMod p →+ G) :
    (AddSubgroup.torsionBy G (2 : ℤ) × ZMod p) → G :=
  fun xa => xa.1.1 + f xa.2

private theorem torsionPairMap_injective
    (hp5 : 5 ≤ p) (f : ZMod p →+ G) (hf : Function.Injective f) :
    Function.Injective (torsionPairMap p f) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  have hdiff : f (a - b) = (y : G) - x := by
    simp only [torsionPairMap] at h
    rw [map_sub]
    calc
      f a - f b = ((x : G) + f a) - f b - x := by abel
      _ = ((y : G) + f b) - f b - x := by rw [h]
      _ = (y : G) - x := by abel
  have htwo_xy : (2 : ℤ) • ((y : G) - x) = 0 := by
    rw [smul_sub]
    have hx : (2 : ℤ) • (x : G) = 0 := x.2
    have hy : (2 : ℤ) • (y : G) = 0 := y.2
    rw [hx, hy, sub_self]
  have htwo_ab : (2 : ℤ) • (a - b) = 0 := by
    apply hf
    rw [map_zero, f.map_zsmul, hdiff, htwo_xy]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hzeroi : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast hzero
    have hdvd : (p : ℤ) ∣ 2 :=
      ZMod.intCast_zmod_eq_zero_iff_dvd 2 p |>.mp hzeroi
    have hp_le_two : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    omega
  have hab : a - b = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h2ne
    simpa [zsmul_eq_mul] using htwo_ab
  have hab' : a = b := sub_eq_zero.mp hab
  subst b
  simp only [torsionPairMap, add_left_inj] at h
  exact Prod.ext (Subtype.ext h) rfl

private theorem torsionPairMap_range_subset_torsion (f : ZMod p →+ G) :
    Set.range (torsionPairMap p f) ⊆
      (AddCommGroup.torsion G : Set G) := by
  rintro _ ⟨⟨x, a⟩, rfl⟩
  change IsOfFinAddOrder ((x : G) + f a)
  apply IsOfFinAddOrder.add
  · rw [isOfFinAddOrder_iff_zsmul_eq_zero]
    exact ⟨2, by norm_num, x.2⟩
  · exact f.isOfFinAddOrder (isOfFinAddOrder_of_finite a)

/-- Full rational two-torsion and an embedded rational `p`-torsion line force at least
`4*p` rational torsion points, once finiteness of the ambient torsion subgroup is known. -/
theorem largeTorsion_of_fullTwoTorsion_of_pEmbedding
    (hp5 : 5 ≤ p)
    (hfinite : (AddCommGroup.torsion G : Set G).Finite)
    (h2 : Set.ncard
      (AddSubgroup.torsionBy G (2 : ℤ) : Set G) = 4)
    (f : ZMod p →+ G) (hf : Function.Injective f) :
    4 * p ≤ Set.ncard (AddCommGroup.torsion G : Set G) := by
  let T2 := AddSubgroup.torsionBy G (2 : ℤ)
  have hcardT2 : Nat.card T2 = 4 := by
    exact (Nat.card_coe_set_eq (T2 : Set G)).trans (by simpa [T2] using h2)
  calc
    4 * p = Nat.card (T2 × ZMod p) := by
      rw [Nat.card_prod, Nat.card_zmod, hcardT2]
    _ = Set.ncard (Set.range (torsionPairMap p f)) :=
      (Set.ncard_range_of_injective
        (torsionPairMap_injective p hp5 f hf)).symm
    _ ≤ Set.ncard (AddCommGroup.torsion G : Set G) :=
      Set.ncard_le_ncard (torsionPairMap_range_subset_torsion p f) hfinite

/-- Elliptic-curve specialization of the generic `4*p` torsion assembly. -/
theorem hasLargeRationalTorsion_of_pEmbedding
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hp5 : 5 ≤ p)
    (hfinite : (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite)
    (h2 : HasFullRationalTwoTorsion E)
    (f : ZMod p →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    HasLargeRationalTorsion E p := by
  exact largeTorsion_of_fullTwoTorsion_of_pEmbedding p hp5 hfinite h2 f hf

/-- Data supplied by the two Serre character cases after the quotient-isogeny construction.
The selected curve is either the original Frey curve or its odd-degree quotient. -/
structure FreyTorsionRouteWitness (p : ℕ) where
  curve : WeierstrassCurve ℚ
  isElliptic : curve.IsElliptic
  fullTwoTorsion : @HasFullRationalTwoTorsion curve isElliptic
  pEmbedding : ZMod p →+ (curve⁄ℚ).Point
  pEmbedding_injective : Function.Injective pEmbedding

attribute [instance] FreyTorsionRouteWitness.isElliptic

/-- Source-provider boundary for the semistable reducible-character theorem, stated over an
abstract representation so the boundary is independent of admitted representation constructors. -/
def ReducibleCharacterContract
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (rho : GaloisRep ℚ (ZMod p) V) : Prop :=
  ¬rho.IsIrreducible →
    Nonempty (SemistableReducibleCharacterDichotomy p V rho)

/-- Geometric boundary: turn either character case into a rational `p`-point on the original
curve or its odd-degree quotient, retaining full rational two-torsion. -/
def CharacterToTorsionRouteContract
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (rho : GaloisRep ℚ (ZMod p) V) : Prop :=
  Nonempty (SemistableReducibleCharacterDichotomy p V rho) →
    Nonempty (FreyTorsionRouteWitness p)

/-- Standard-axiom replacement boundary for the numerical consequence of Mazur's theorem. -/
def RationalTorsionBound16ForAll : Prop :=
  ∀ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic), @RationalTorsionBound16 E hE

/-- Once the deep character, quotient geometry, and Mazur torsion providers are available,
irreducibility is a kernel-clean assembly theorem. -/
theorem irreducible_of_component_contracts
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (rho : GaloisRep ℚ (ZMod p) V)
    (hp5 : 5 ≤ p)
    (hcharacter : ReducibleCharacterContract p rho)
    (hgeometry : CharacterToTorsionRouteContract p rho)
    (hmazur : RationalTorsionBound16ForAll) : rho.IsIrreducible := by
  by_contra hirred
  let W := (hgeometry (hcharacter hirred)).some
  have hbound : RationalTorsionBound16 W.curve := hmazur W.curve W.isElliptic
  have hlarge : HasLargeRationalTorsion W.curve p :=
    hasLargeRationalTorsion_of_pEmbedding p W.curve hp5 hbound.1
      W.fullTwoTorsion W.pEmbedding W.pEmbedding_injective
  exact not_hasLargeRationalTorsion_of_bound16 W.curve p hp5 hbound hlarge

#check largeTorsion_of_fullTwoTorsion_of_pEmbedding
#check hasLargeRationalTorsion_of_pEmbedding
#check ReducibleCharacterContract
#check CharacterToTorsionRouteContract
#check RationalTorsionBound16ForAll
#check irreducible_of_component_contracts

#print axioms largeTorsion_of_fullTwoTorsion_of_pEmbedding
#print axioms hasLargeRationalTorsion_of_pEmbedding
#print axioms ReducibleCharacterContract
#print axioms CharacterToTorsionRouteContract
#print axioms RationalTorsionBound16ForAll
#print axioms irreducible_of_component_contracts

end
end FLTMethodology.Mazur
