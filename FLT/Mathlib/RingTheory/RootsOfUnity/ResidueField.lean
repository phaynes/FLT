/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Roots of unity and residue fields

Material destined for Mathlib. This file separates two elementary facts used by the tame-residue
construction:

* reduction is injective on roots of unity whose exponent is a unit in a local ring;
* the units of a finite field exhaust the roots of `X ^ (q - 1) - 1` in any domain containing it.

Neither result uses Henselian lifting or local class-field theory.
-/

@[expose] public section

noncomputable section

open Finset IsLocalRing

/-- A root of unity of unit order which reduces to one in a local ring is one. -/
theorem eq_one_of_pow_eq_one_of_residue_eq_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {u : R}
    (hpow : u ^ n = 1)
    (hres : residue R u = 1) :
    u = 1 := by
  let s : R := ∑ i ∈ range n, u ^ i
  have hsres : residue R s = (n : ResidueField R) := by
    simp [s, hres]
  have hsnz : residue R s ≠ 0 := by
    rw [hsres]
    exact (hn.map (residue R)).ne_zero
  have hsunit : IsUnit s := (residue_ne_zero_iff_isUnit s).mp hsnz
  have hprod : s * (u - 1) = 0 := by
    simpa [s, hpow] using geom_sum_mul u n
  apply sub_eq_zero.mp
  exact hsunit.mul_left_cancel (by simpa using hprod)

/-- Reduction is injective on roots of unity whose exponent is a unit in the local ring. -/
theorem rootsOfUnity_residue_injective
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Injective (restrictRootsOfUnity (residue R) n) := by
  refine (injective_iff_map_eq_one _).mpr fun z hz ↦ ?_
  apply Subtype.ext
  apply Units.ext
  change ((z : Rˣ) : R) = 1
  apply eq_one_of_pow_eq_one_of_residue_eq_one hn
  · simpa using congrArg (fun w : Rˣ ↦ (w : R)) z.prop
  · simpa using congrArg
      (fun w : rootsOfUnity n (ResidueField R) ↦
        ((w : (ResidueField R)ˣ) : ResidueField R)) hz

/-- The canonical map from the units of a finite field into the `(q - 1)`-st roots of unity in a
domain containing that field. -/
noncomputable def finiteFieldUnitsToRootsOfUnity
    (k L : Type*) [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) : kˣ →* rootsOfUnity (Nat.card k - 1) L := by
  letI := Fintype.ofFinite k
  exact
    { toFun := fun u ↦ ⟨Units.map f u, by
        rw [mem_rootsOfUnity]
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
        rw [← map_pow]
        simpa [Nat.card_eq_fintype_card] using
          congrArg f (FiniteField.pow_card_sub_one_eq_one (u : k) (Units.ne_zero u))⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        simp
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        apply Units.ext
        simp }

/-- The canonical finite-field unit map is injective when the underlying ring homomorphism is. -/
theorem finiteFieldUnitsToRootsOfUnity_injective
    {k L : Type*} [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) (hf : Function.Injective f) :
    Function.Injective (finiteFieldUnitsToRootsOfUnity k L f) := by
  intro x y hxy
  apply Units.ext
  apply hf
  have h := congrArg
    (fun z : rootsOfUnity (Nat.card k - 1) L ↦ ((z : Lˣ) : L)) hxy
  simpa [finiteFieldUnitsToRootsOfUnity] using h

/-- The canonical finite-field unit map exhausts all `(q - 1)`-st roots in the target domain. -/
theorem finiteFieldUnitsToRootsOfUnity_bijective
    {k L : Type*} [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) (hf : Function.Injective f) :
    Function.Bijective (finiteFieldUnitsToRootsOfUnity k L f) := by
  have hnpos : 0 < Nat.card k - 1 := Nat.sub_pos_iff_lt.mpr Finite.one_lt_card
  letI : NeZero (Nat.card k - 1) := ⟨hnpos.ne'⟩
  have hinj := finiteFieldUnitsToRootsOfUnity_injective f hf
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨hinj, le_antisymm (Nat.card_le_card_of_injective _ hinj) ?_⟩
  simpa only [Nat.card_units] using card_rootsOfUnity L (Nat.card k - 1)

/-- The units of a finite field are canonically equivalent to the `(q - 1)`-st roots of unity in
any domain into which the field embeds. -/
noncomputable def finiteFieldUnitsEquivRootsOfUnity
    (k L : Type*) [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) (hf : Function.Injective f) :
    kˣ ≃* rootsOfUnity (Nat.card k - 1) L :=
  MulEquiv.ofBijective (finiteFieldUnitsToRootsOfUnity k L f)
    (finiteFieldUnitsToRootsOfUnity_bijective f hf)

end
