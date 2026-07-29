/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!

Let E be an elliptic curve over the field of fractions k
of a DVR, with good reduction. Let n be a positive
integer which is nonzero in k.
Then the Galois representation on the n-torsion points
over k^sep is unramified.

This is the easy direction of the criterion of Néron–Ogg–Shafarevich;
see for example [Silverman, *The Arithmetic of Elliptic Curves*, VII.7.1]
or [Serre–Tate, *Good reduction of abelian varieties*, Theorem 1
for the general abelian variety case].

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element of the inertia subgroup acts trivially on the residue field. This is the
pointwise form of the kernel condition in `ValuationSubring.inertiaSubgroup`. -/
theorem inertia_smul_residue_eq (A : ValuationSubring L)
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (x : IsLocalRing.ResidueField A) : σ • x = x := by
  have hσ' :
      MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) σ = 1 := hσ
  exact DFunLike.congr_fun hσ' x

/-- Reduction of an integral element is unchanged by an element of inertia. -/
theorem inertia_residue_smul_eq (A : ValuationSubring L)
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (x : A) :
    algebraMap A (IsLocalRing.ResidueField A) (σ • x) =
      algebraMap A (IsLocalRing.ResidueField A) x := by
  simpa using A.inertia_smul_residue_eq K σ hσ
    (algebraMap A (IsLocalRing.ResidueField A) x)

/-- The base ring maps into a valuation subring whose intersection with the base field is the
given image of that ring. -/
noncomputable def baseRingHom (R : Type*) [CommRing R] [Algebra R K]
    (A : ValuationSubring L)
    (hA : (A.comap (algebraMap K L)).toSubring = (algebraMap R K).range) : R →+* A :=
  ((algebraMap K L).comp (algebraMap R K)).codRestrict A.toSubring fun r ↦ by
    have hr : algebraMap R K r ∈ (algebraMap R K).range := ⟨r, rfl⟩
    rw [← hA] at hr
    exact hr

@[simp]
theorem coe_baseRingHom (R : Type*) [CommRing R] [Algebra R K]
    (A : ValuationSubring L)
    (hA : (A.comap (algebraMap K L)).toSubring = (algebraMap R K).range) (r : R) :
    ((A.baseRingHom K R hA r : A) : L) =
      algebraMap K L (algebraMap R K r) :=
  rfl

/-- The map from the base ring to a valuation subring lying above it is local when the base ring
has the given field as its fraction field. -/
theorem isLocalHom_baseRingHom (R : Type*) [CommRing R] [IsDomain R]
    [Algebra R K] [IsFractionRing R K] (A : ValuationSubring L)
    (hA : (A.comap (algebraMap K L)).toSubring = (algebraMap R K).range) :
    IsLocalHom (A.baseRingHom K R hA) := by
  constructor
  intro r hr
  obtain ⟨u, hu⟩ := hr
  have hur : ((u : A) : L) = algebraMap K L (algebraMap R K r) := by
    rw [hu]
    rfl
  have hinv_mem : algebraMap K L (algebraMap R K r)⁻¹ ∈ A := by
    rw [map_inv₀, ← hur]
    have huinv : ((((u⁻¹ : Aˣ) : A) : L)) = (((u : A) : L))⁻¹ := by
      change ((Units.map A.subtype.toMonoidHom (u⁻¹) : Lˣ) : L) =
        ((Units.map A.subtype.toMonoidHom u : Lˣ) : L)⁻¹
      rw [map_inv]
      exact Units.val_inv_eq_inv_val _
    rw [← huinv]
    exact (u⁻¹ : Aˣ).val.property
  have hinv_comap : (algebraMap R K r)⁻¹ ∈ A.comap (algebraMap K L) :=
    hinv_mem
  have hinv_range : (algebraMap R K r)⁻¹ ∈ (algebraMap R K).range := by
    rw [← hA]
    exact hinv_comap
  obtain ⟨s, hs⟩ := hinv_range
  have hrK : algebraMap R K r ≠ 0 := by
    intro hr0
    have hu0 : ((u : A) : L) = 0 := by rw [hur, hr0, map_zero]
    exact u.ne_zero (Subtype.ext hu0)
  apply isUnit_iff_exists.mpr
  refine ⟨s, ?_, ?_⟩
  · apply IsFractionRing.injective R K
    simpa [map_mul, hs] using mul_inv_cancel₀ hrK
  · rw [mul_comm]
    apply IsFractionRing.injective R K
    simpa [map_mul, hs] using mul_inv_cancel₀ hrK

end ValuationSubring

/-- A reduction map which is injective on `n`-torsion and invariant under a collection
of field automorphisms proves that those automorphisms fix the `n`-torsion. The geometric
content of good reduction is isolated in the two hypotheses, while preservation of
torsion by base change is discharged here. -/
theorem WeierstrassCurve.torsion_fixed_of_invariant_injective
    {k ksep : Type*} [Field k] [Field ksep] [Algebra k ksep]
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq ksep]
    (n : ℕ) {G : Type*} [Group G]
    (act : G → ksep ≃ₐ[k] ksep) {β : Type*}
    (I : Set G)
    (reduce : (E⁄ksep).Point → β)
    (hinj : Set.InjOn reduce (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)))
    (hinvariant : ∀ σ ∈ I, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      reduce (Affine.Point.map (act σ).toAlgHom P) = reduce P) :
    ∀ σ ∈ I, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (act σ).toAlgHom P = P := by
  intro σ hσ P hP
  apply hinj
  · change Affine.Point.map (act σ).toAlgHom P ∈
      AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)
    rw [AddSubgroup.torsionBy.nsmul_iff]
    have hP' : n • P = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hP
    calc
      n • Affine.Point.map (act σ).toAlgHom P =
          Affine.Point.map (act σ).toAlgHom (n • P) :=
        ((Affine.Point.map (W' := E) (act σ).toAlgHom).map_nsmul n P).symm
      _ = 0 := by rw [hP']; exact map_zero (Affine.Point.map (W' := E) _)
  · exact hP
  · exact hinvariant σ hσ P hP

-- let R be a discrete valuation ring with field of fractions k
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]

-- Let E/k be an elliptic curve with good reduction over R. Note that mathlib's
-- `HasGoodReduction` asks that the given Weierstrass equation for E is a minimal
-- integral equation whose discriminant has valuation 1; this loses no generality
-- because every elliptic curve over k is isomorphic to one given by a minimal
-- equation (`WeierstrassCurve.exists_isMinimal`).
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]

-- Let ksep be a separable closure of k (`DecidableEq` is needed for the group law on points)
variable (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] [DecidableEq ksep]

-- Let 𝒪 be a valuation subring of ksep. This is arbitrary here; the hypothesis
-- that it lies above R is `h𝒪` in the theorem below.
variable (𝒪 : ValuationSubring ksep)

/-- If `E` is an elliptic curve over `k` (given by a minimal Weierstrass equation)
with good reduction over `R`, and if `𝒪` is a valuation subring of `kˢᵉᵖ` lying above `R`,
then the inertia subgroup of `Gal(kˢᵉᵖ/k)` at `𝒪` acts trivially on the `n`-torsion
of `E(kˢᵉᵖ)`. In other words, the Galois representation on the `n`-torsion points
is unramified. -/
theorem WeierstrassCurve.torsion_unramified_of_good_reduction
    -- Assume 𝒪 lies above R, i.e. 𝒪 ∩ k = R
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    -- Then every element of the inertia subgroup at 𝒪 fixes every n-torsion point of E(ksep)
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P :=
  sorry
