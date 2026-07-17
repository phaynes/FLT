import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Kernel probe for the coefficient-independent Tier-1 p-adic-Hodge vocabulary.

This file deliberately provides only global weight data, the Fontaine--Laffaille interval,
unramifiedness of the rational prime, dualisation of a Galois representation, and two guards.
It does not define crystallinity or extract Hodge--Tate weights from a representation. Those
provider theorems remain explicit graph gaps.
-/

namespace FLTMethodology.Taylor2018

open NumberField

/-- Hodge--Tate weight data indexed by global embeddings of the base number field. -/
def AbstractWeightData
    (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  (F →+* AlgebraicClosure ℚ_[ℓ]) → Multiset ℤ

/-- A rank-sized, pairwise-distinct multiset at every global embedding. -/
def IsRegularWeightData
    {F : Type*} [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime]
    (rank : ℕ) (w : AbstractWeightData F ℓ) : Prop :=
  ∀ τ, (w τ).card = rank ∧ (w τ).Nodup

/-- Pointwise equality of two global weight data. -/
def HodgeTateWeightsMatch
    {F : Type*} [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime]
    (w₁ w₂ : AbstractWeightData F ℓ) : Prop :=
  ∀ τ, w₁ τ = w₂ τ

/-- Every weight lies in one globally shared Fontaine--Laffaille interval. -/
def InFontaineLaffailleInterval
    {F : Type*} [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime]
    (a : ℤ) (w : AbstractWeightData F ℓ) : Prop :=
  ∀ τ n, n ∈ w τ → n ∈ Set.Icc a (a + (ℓ : ℤ) - 2)

/-- The rational prime `ℓ` is unramified in the ring of integers of `F`. -/
def EllUnramifiedInIntegers
    (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ : ℤ)})

/-- The coefficient-independent Tier-1 weight and local-number-field bundle. -/
structure AbstractWeightLocalData
    (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) [Fact ℓ.Prime] (rank : ℕ) where
  weights : AbstractWeightData F ℓ
  regular : IsRegularWeightData rank weights
  intervalBase : ℤ
  inInterval : InFontaineLaffailleInterval intervalBase weights
  ellUnramified : EllUnramifiedInIntegers F ℓ

private noncomputable def endTranspose
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M] :
    Module.End A M →ₗ[A] Module.End A (Module.Dual A M) where
  toFun f := f.dualMap
  map_add' f g := by ext φ m; simp
  map_smul' a f := by ext φ m; simp

/-- The contragredient Galois representation on the module dual. -/
noncomputable def GaloisRepDual
    {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) :
    GaloisRep K A (Module.Dual A M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A (Module.Dual A M))
  letI := IsModuleTopology.toContinuousAdd A (Module.End A (Module.Dual A M))
  { toFun σ := (ρ σ⁻¹).dualMap
    map_one' := by ext φ m; simp
    map_mul' σ τ := by ext φ m; simp
    continuous_toFun := by
      have hρ : Continuous ρ := ρ.continuous_toFun
      have ht : Continuous (endTranspose (A := A) (M := M)) :=
        IsModuleTopology.continuous_of_linearMap _
      exact ht.comp (hρ.comp continuous_inv) }

/-- The weight-two multiset `{-1, 0}` fits the prescribed interval exactly when `2 < ℓ`. -/
lemma weightTwo_fits_iff_two_lt
    {F : Type*} [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime] :
    (∃ a : ℤ,
      InFontaineLaffailleInterval (F := F) (ℓ := ℓ) a
        (fun _ => ({-1, 0} : Multiset ℤ))) ↔
    2 < ℓ := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨τ⟩ := (inferInstance : Nonempty (F →+* AlgebraicClosure ℚ_[ℓ]))
    have hneg := ha τ (-1) (by simp)
    have hzero := ha τ 0 (by simp)
    have ha_le_neg_one : a ≤ -1 := hneg.1
    have hzero_le_top : 0 ≤ a + (ℓ : ℤ) - 2 := hzero.2
    have hthree : (3 : ℤ) ≤ (ℓ : ℤ) := by omega
    exact_mod_cast hthree
  · intro hℓ
    refine ⟨-1, fun τ n hn => ?_⟩
    have hthree : (3 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
    have hn' : n = -1 ∨ n = 0 := by simpa using hn
    rcases hn' with rfl | rfl <;> constructor <;> omega

/-- A repeated weight multiset cannot satisfy regularity. -/
lemma repeatedWeightTwo_not_regular
    {F : Type*} [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime] :
    ¬ IsRegularWeightData (F := F) (ℓ := ℓ) 2
        (fun _ => ({0, 0} : Multiset ℤ)) := by
  intro h
  obtain ⟨τ⟩ := (inferInstance : Nonempty (F →+* AlgebraicClosure ℚ_[ℓ]))
  have hnodup := (h τ).2
  simp at hnodup

#check AbstractWeightData
#check IsRegularWeightData
#check HodgeTateWeightsMatch
#check InFontaineLaffailleInterval
#check EllUnramifiedInIntegers
#check AbstractWeightLocalData
#check GaloisRepDual
#check weightTwo_fits_iff_two_lt
#check repeatedWeightTwo_not_regular

#print axioms AbstractWeightData
#print axioms IsRegularWeightData
#print axioms HodgeTateWeightsMatch
#print axioms InFontaineLaffailleInterval
#print axioms EllUnramifiedInIntegers
#print axioms AbstractWeightLocalData
#print axioms GaloisRepDual
#print axioms weightTwo_fits_iff_two_lt
#print axioms repeatedWeightTwo_not_regular

end FLTMethodology.Taylor2018
