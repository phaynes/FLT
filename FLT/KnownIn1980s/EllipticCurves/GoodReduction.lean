/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import FLT.EllipticCurve.TorsionProof.RootSeparation

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

section ProjectiveNormalization

variable {F : Type*} [Field F]

open scoped WeierstrassCurve.Projective

/-- An integral vector has a unit coordinate. -/
def HasUnitCoordinate (A : ValuationSubring F) (P : Fin 3 → A) : Prop :=
  ∃ i, IsUnit (P i)

/-- Integral coordinates obtained from a nonzero vector by a nonzero scalar, with a unit
coordinate. -/
structure UnitCoordinateNormalization (A : ValuationSubring F) (P : Fin 3 → F) where
  scale : F
  scale_ne_zero : scale ≠ 0
  coords : Fin 3 → A
  coe_coords : ∀ i, (coords i : F) = scale * P i
  hasUnitCoordinate : A.HasUnitCoordinate coords

/-- A nonzero vector of length three over the fraction field of a valuation subring admits
integral coordinates with a unit coordinate. -/
theorem exists_unitCoordinateNormalization (A : ValuationSubring F) (P : Fin 3 → F)
    (hP : P ≠ 0) : Nonempty (A.UnitCoordinateNormalization P) := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ A.valuation (P i))
    Finset.univ_nonempty
  obtain ⟨i, hi⟩ : ∃ i, P i ≠ 0 := by
    by_contra h
    apply hP
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hPj : P j ≠ 0 := by
    intro hPj
    have hij := hj i (Finset.mem_univ i)
    rw [hPj, map_zero] at hij
    exact (not_le_of_gt (A.valuation.pos_iff.mpr hi)) hij
  have hdiv (i : Fin 3) : ∃ a : A, (a : F) * P j = P i :=
    (A.valuation_le_iff (P i) (P j)).mp (hj i (Finset.mem_univ i))
  let Q : Fin 3 → A := fun i ↦ (hdiv i).choose
  have hQ (i : Fin 3) : (Q i : F) * P j = P i :=
    (hdiv i).choose_spec
  refine ⟨⟨(P j)⁻¹, inv_ne_zero hPj, Q, ?_, ?_⟩⟩
  · intro i
    rw [← hQ i]
    field_simp
  · refine ⟨j, ?_⟩
    have hQj : Q j = 1 := by
      apply Subtype.ext
      exact mul_right_cancel₀ hPj (by simpa using hQ j)
    rw [hQj]
    exact isUnit_one

/-- Coordinatewise reduction of an integral vector. -/
noncomputable def residueVector (A : ValuationSubring F) (P : Fin 3 → A) :
    Fin 3 → IsLocalRing.ResidueField A :=
  fun i ↦ algebraMap A (IsLocalRing.ResidueField A) (P i)

/-- A vector with a unit coordinate has nonzero residue reduction. -/
theorem residueVector_ne_zero (A : ValuationSubring F) (P : Fin 3 → A)
    (hP : A.HasUnitCoordinate P) : A.residueVector P ≠ 0 := by
  obtain ⟨i, hi⟩ := hP
  intro hzero
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (P i)).mpr hi <| by
    simpa [residueVector] using congrFun hzero i

/-- Two integral vectors with unit coordinates which differ by a field scalar already differ by
a unit scalar in the valuation subring. -/
theorem exists_unit_smul_eq_of_scaled
    (A : ValuationSubring F) (P Q : Fin 3 → A)
    (hP : A.HasUnitCoordinate P) (hQ : A.HasUnitCoordinate Q)
    (c : F) (hc : ∀ i, (Q i : F) = c * (P i : F)) :
    ∃ u : A, IsUnit u ∧ Q = u • P := by
  obtain ⟨i, hi⟩ := hP
  let u : A := Q i * (hi.unit⁻¹ : Aˣ)
  have hiF : (((hi.unit⁻¹ : Aˣ) : A) : F) = ((P i : A) : F)⁻¹ := by
    change ((Units.map A.subtype.toMonoidHom hi.unit⁻¹ : Fˣ) : F) = ((P i : A) : F)⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val]
    congr 1
  have hPi : ((P i : A) : F) ≠ 0 := by
    exact_mod_cast hi.ne_zero
  have huF : (u : F) = c := by
    change (Q i : F) * (((hi.unit⁻¹ : Aˣ) : A) : F) = c
    rw [hiF, hc i, mul_assoc, mul_inv_cancel₀ hPi, mul_one]
  have hQP : Q = u • P := by
    funext j
    apply Subtype.ext
    simpa [huF] using hc j
  refine ⟨u, ?_, hQP⟩
  obtain ⟨j, hj⟩ := hQ
  have hQj : IsUnit (u * P j) := by
    simpa [hQP] using hj
  exact isUnit_of_mul_isUnit_left hQj

/-- Residue projective classes are unchanged when primitive integral representatives differ by a
field scalar. -/
theorem residue_pointClass_eq_of_scaled
    (A : ValuationSubring F) (P Q : Fin 3 → A)
    (hP : A.HasUnitCoordinate P) (hQ : A.HasUnitCoordinate Q)
    (c : F) (hc : ∀ i, (Q i : F) = c * (P i : F)) :
    (⟦A.residueVector Q⟧ : WeierstrassCurve.Projective.PointClass
      (IsLocalRing.ResidueField A)) = ⟦A.residueVector P⟧ := by
  obtain ⟨u, hu, rfl⟩ := A.exists_unit_smul_eq_of_scaled P Q hP hQ c hc
  have hres : A.residueVector (u • P) =
      algebraMap A (IsLocalRing.ResidueField A) u • A.residueVector P := by
    ext i
    simp [residueVector]
  rw [hres, WeierstrassCurve.Projective.smul_eq _ (hu.map <| algebraMap A _)]

/-- A chosen unit-coordinate normalization of a nonzero vector. -/
noncomputable def unitCoordinateNormalization (A : ValuationSubring F) (P : Fin 3 → F)
    (hP : P ≠ 0) : A.UnitCoordinateNormalization P :=
  Classical.choice (A.exists_unitCoordinateNormalization P hP)

/-- The residue representative selected from a field-valued vector, with the zero vector sent to
zero. -/
noncomputable def residueRepresentative (A : ValuationSubring F) (P : Fin 3 → F) :
    Fin 3 → IsLocalRing.ResidueField A := by
  classical
  exact if hP : P = 0 then 0
    else A.residueVector (A.unitCoordinateNormalization P hP).coords

theorem residueRepresentative_of_ne_zero (A : ValuationSubring F) (P : Fin 3 → F)
    (hP : P ≠ 0) : A.residueRepresentative P =
      A.residueVector (A.unitCoordinateNormalization P hP).coords := by
  classical
  simp [residueRepresentative, hP]

/-- The residue representative of a nonzero vector is nonzero. -/
theorem residueRepresentative_ne_zero (A : ValuationSubring F) (P : Fin 3 → F)
    (hP : P ≠ 0) : A.residueRepresentative P ≠ 0 := by
  rw [A.residueRepresentative_of_ne_zero P hP]
  exact A.residueVector_ne_zero _ (A.unitCoordinateNormalization P hP).hasUnitCoordinate

/-- Unit scaling over the fraction field does not change the residue projective class selected by
unit-coordinate normalization. -/
theorem residue_pointClass_unit_smul (A : ValuationSubring F) (P : Fin 3 → F) (u : Fˣ) :
    (⟦A.residueRepresentative (u • P)⟧ : WeierstrassCurve.Projective.PointClass
      (IsLocalRing.ResidueField A)) = ⟦A.residueRepresentative P⟧ := by
  classical
  by_cases hP : P = 0
  · subst P
    simp [residueRepresentative]
  · have huP : u • P ≠ 0 := smul_ne_zero u.ne_zero hP
    rw [A.residueRepresentative_of_ne_zero (u • P) huP,
      A.residueRepresentative_of_ne_zero P hP]
    let NP := A.unitCoordinateNormalization P hP
    let NQ := A.unitCoordinateNormalization (u • P) huP
    apply A.residue_pointClass_eq_of_scaled NP.coords NQ.coords
      NP.hasUnitCoordinate NQ.hasUnitCoordinate
      (NQ.scale * (u : F) * NP.scale⁻¹)
    intro i
    rw [NQ.coe_coords, NP.coe_coords]
    change NQ.scale * ((u : F) * P i) =
      (NQ.scale * (u : F) * NP.scale⁻¹) * (NP.scale * P i)
    field_simp [NP.scale_ne_zero]

/-- Residue reduction of unit-normalized vectors descends to projective point classes. -/
noncomputable def projectiveResidue (A : ValuationSubring F) :
    WeierstrassCurve.Projective.PointClass F →
      WeierstrassCurve.Projective.PointClass (IsLocalRing.ResidueField A) :=
  Quotient.map A.residueRepresentative fun _ _ h ↦ by
    rcases h with ⟨u, rfl⟩
    exact Quotient.eq.mp (A.residue_pointClass_unit_smul _ u)

theorem projectiveResidue_mk (A : ValuationSubring F) (P : Fin 3 → F) :
    A.projectiveResidue ⟦P⟧ = ⟦A.residueRepresentative P⟧ :=
  rfl

/-- A primitive integral representative reduces coordinatewise. -/
theorem projectiveResidue_mk_integral (A : ValuationSubring F)
    (P : Fin 3 → A) (hP : A.HasUnitCoordinate P) :
    A.projectiveResidue ⟦fun i => (P i : F)⟧ =
      (⟦A.residueVector P⟧ : WeierstrassCurve.Projective.PointClass
        (IsLocalRing.ResidueField A)) := by
  let PF : Fin 3 → F := fun i => (P i : F)
  have hPF : PF ≠ 0 := by
    obtain ⟨i, hi⟩ := hP
    intro hz
    have hzi := congrFun hz i
    exact hi.ne_zero (A.subtype_injective hzi)
  rw [show (fun i => (P i : F)) = PF from rfl, A.projectiveResidue_mk,
    A.residueRepresentative_of_ne_zero PF hPF]
  exact A.residue_pointClass_eq_of_scaled P
    (A.unitCoordinateNormalization PF hPF).coords hP
    (A.unitCoordinateNormalization PF hPF).hasUnitCoordinate
    (A.unitCoordinateNormalization PF hPF).scale
    (A.unitCoordinateNormalization PF hPF).coe_coords

/-- Equality of reductions of integral affine triples is coordinatewise equality in the residue
field. -/
theorem residue_affine_coords_eq_of_projectiveResidue_eq
    (A : ValuationSubring F) (x₁ y₁ x₂ y₂ : A)
    (h : A.projectiveResidue ⟦fun i => ((![x₁, y₁, 1] : Fin 3 → A) i : F)⟧ =
      A.projectiveResidue ⟦fun i => ((![x₂, y₂, 1] : Fin 3 → A) i : F)⟧) :
    algebraMap A (IsLocalRing.ResidueField A) x₁ =
        algebraMap A (IsLocalRing.ResidueField A) x₂ ∧
      algebraMap A (IsLocalRing.ResidueField A) y₁ =
        algebraMap A (IsLocalRing.ResidueField A) y₂ := by
  let P : Fin 3 → A := ![x₁, y₁, 1]
  let Q : Fin 3 → A := ![x₂, y₂, 1]
  have hP : A.HasUnitCoordinate P := ⟨2, isUnit_one⟩
  have hQ : A.HasUnitCoordinate Q := ⟨2, isUnit_one⟩
  rw [show (fun i => ((![x₁, y₁, 1] : Fin 3 → A) i : F)) =
      (fun i => (P i : F)) from rfl,
    show (fun i => ((![x₂, y₂, 1] : Fin 3 → A) i : F)) =
      (fun i => (Q i : F)) from rfl,
    A.projectiveResidue_mk_integral P hP,
    A.projectiveResidue_mk_integral Q hQ] at h
  have hequiv : A.residueVector P ≈ A.residueVector Q := Quotient.eq.mp h
  have hvec : A.residueVector P = A.residueVector Q :=
    (WeierstrassCurve.Projective.equiv_iff_eq_of_Z_eq
      (by simp [ValuationSubring.residueVector, P, Q])
      (by simp [ValuationSubring.residueVector, Q])).mp hequiv
  constructor
  · simpa [ValuationSubring.residueVector, P, Q] using congrFun hvec 0
  · simpa [ValuationSubring.residueVector, P, Q] using congrFun hvec 1

end ProjectiveNormalization

end ValuationSubring

namespace WeierstrassCurve.Projective

variable {F : Type*} [Field F] {W : WeierstrassCurve.Projective F}

/-- On an elliptic Weierstrass curve over a field, every nonzero projective solution is
nonsingular. -/
theorem nonsingular_of_equation_of_ne_zero [W.IsElliptic] {P : Fin 3 → F}
    (hP : W.Equation P) (hP0 : P ≠ 0) : W.Nonsingular P := by
  by_cases hPz : P 2 = 0
  · have hPx : P 0 = 0 := X_eq_zero_of_Z_eq_zero hP hPz
    have hPy : P 1 ≠ 0 := by
      intro hPy
      apply hP0
      funext i
      fin_cases i <;> assumption
    exact (nonsingular_of_Z_eq_zero hPz).mpr ⟨hP, by simp [hPx, hPy]⟩
  · rw [nonsingular_of_Z_ne_zero hPz, ← Affine.equation_iff_nonsingular]
    exact (equation_of_Z_ne_zero hPz).mp hP

/-- A nonsingular projective representative is not the zero vector. -/
theorem Nonsingular.ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  intro hzero
  subst P
  simp [nonsingular_iff] at hP

end WeierstrassCurve.Projective

namespace ValuationSubring

section PointSpecialization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
variable {ksep : Type*} [Field ksep] [Algebra k ksep]

open scoped WeierstrassCurve.Projective

/-- The integral model over a valuation subring lying above the original discrete valuation
ring. -/
noncomputable def extendedIntegralModel (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsMinimal R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    WeierstrassCurve A :=
  (E.integralModel R).map (A.baseRingHom k R hA)

/-- Extending the integral model to the separable field recovers the original Weierstrass
curve after base change. -/
theorem map_extendedIntegralModel_eq (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsMinimal R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    (A.extendedIntegralModel R k E hA).map A.subtype = E.map (algebraMap k ksep) := by
  ext <;> simp [extendedIntegralModel, coe_baseRingHom,
    WeierstrassCurve.integralModel_a₁_eq, WeierstrassCurve.integralModel_a₂_eq,
    WeierstrassCurve.integralModel_a₃_eq, WeierstrassCurve.integralModel_a₄_eq,
    WeierstrassCurve.integralModel_a₆_eq]

/-- The residue-field map induced by the local inclusion of the original discrete valuation
ring into the valuation subring. -/
noncomputable def baseResidueMap (A : ValuationSubring ksep)
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField A := by
  letI : IsLocalHom (A.baseRingHom k R hA) :=
    A.isLocalHom_baseRingHom k R hA
  exact IsLocalRing.ResidueField.map (A.baseRingHom k R hA)

/-- Reducing the extended integral model agrees with reducing first over the discrete valuation
ring and then extending residue fields. -/
theorem residue_extendedIntegralModel_eq (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsMinimal R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    (A.extendedIntegralModel R k E hA).map
        (algebraMap A (IsLocalRing.ResidueField A)) =
      (E.reduction R).map
        (A.baseResidueMap R k hA) := by
  ext <;> simp [extendedIntegralModel, baseResidueMap, WeierstrassCurve.reduction]

/-- Inertia does not change the projective residue class selected by unit-coordinate
normalization. -/
theorem projectiveResidue_inertia (A : ValuationSubring ksep)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (P : Fin 3 → ksep) :
    (⟦A.residueRepresentative (fun i ↦ σ • P i)⟧ :
      WeierstrassCurve.Projective.PointClass (IsLocalRing.ResidueField A)) =
      ⟦A.residueRepresentative P⟧ := by
  classical
  by_cases hP : P = 0
  · subst P
    have hz : (fun i : Fin 3 ↦ σ • (0 : Fin 3 → ksep) i) = 0 := by
      funext i
      simp
    rw [hz]
  · let σP : Fin 3 → ksep := fun i ↦ σ • P i
    have hσP : σP ≠ 0 := by
      intro hzero
      apply hP
      funext i
      have hz := congrFun hzero i
      change σ.1 (P i) = 0 at hz
      exact σ.1.injective (hz.trans (map_zero σ.1).symm)
    rw [show (fun i ↦ σ • P i) = σP from rfl,
      A.residueRepresentative_of_ne_zero σP hσP,
      A.residueRepresentative_of_ne_zero P hP]
    let NP := A.unitCoordinateNormalization P hP
    let Nσ := A.unitCoordinateNormalization σP hσP
    let Q : Fin 3 → A := fun i ↦ σ • NP.coords i
    have hQunit : A.HasUnitCoordinate Q := by
      obtain ⟨i, hi⟩ := NP.hasUnitCoordinate
      refine ⟨i, ?_⟩
      exact hi.map (MulSemiringAction.toRingAut (A.decompositionSubgroup k) A σ).toRingHom
    have hQcoe (i : Fin 3) : (Q i : ksep) = σ.1 (NP.scale) * σ.1 (P i) := by
      change σ.1 (NP.coords i : ksep) = σ.1 (NP.scale) * σ.1 (P i)
      rw [NP.coe_coords, map_mul]
    have hscale : ∀ i, (Nσ.coords i : ksep) =
        (Nσ.scale * (σ.1 NP.scale)⁻¹) * (Q i : ksep) := by
      intro i
      rw [Nσ.coe_coords, hQcoe]
      change Nσ.scale * σ.1 (P i) =
        (Nσ.scale * (σ.1 NP.scale)⁻¹) *
          (σ.1 NP.scale * σ.1 (P i))
      field_simp [NP.scale_ne_zero]
    have hclass :
        (⟦A.residueVector Nσ.coords⟧ : WeierstrassCurve.Projective.PointClass
          (IsLocalRing.ResidueField A)) = ⟦A.residueVector Q⟧ :=
      A.residue_pointClass_eq_of_scaled Q Nσ.coords hQunit Nσ.hasUnitCoordinate
        _ hscale
    have hres : A.residueVector Q = A.residueVector NP.coords := by
      funext i
      exact A.inertia_residue_smul_eq k σ hσ (NP.coords i)
    exact hclass.trans (congrArg (fun V ↦
      (⟦V⟧ : WeierstrassCurve.Projective.PointClass
        (IsLocalRing.ResidueField A))) hres)

/-- Unit-coordinate normalization followed by residue reduction preserves the projective
Weierstrass equation of the extended integral model. -/
theorem residueRepresentative_equation (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsMinimal R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (P : Fin 3 → ksep) (hP : P ≠ 0)
    (hEq : (E.map (algebraMap k ksep)).toProjective.Equation P) :
    ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.Equation
      (A.residueRepresentative P) := by
  let N := A.unitCoordinateNormalization P hP
  have hEqScaled : (E.map (algebraMap k ksep)).toProjective.Equation (N.scale • P) :=
    (WeierstrassCurve.Projective.equation_smul P
      (isUnit_iff_ne_zero.mpr N.scale_ne_zero)).mpr hEq
  have hMapEq :
      ((A.extendedIntegralModel R k E hA).map A.subtype).toProjective.Equation
        (A.subtype ∘ N.coords) := by
    rw [A.map_extendedIntegralModel_eq R k E hA]
    convert hEqScaled using 1
    funext i
    exact N.coe_coords i
  have hIntegralEq :
      (A.extendedIntegralModel R k E hA).toProjective.Equation N.coords :=
    (WeierstrassCurve.Projective.map_equation (W' :=
      (A.extendedIntegralModel R k E hA).toProjective) A.subtype_injective N.coords).mp hMapEq
  have hReducedEq :
      ((A.extendedIntegralModel R k E hA).map
        (algebraMap A (IsLocalRing.ResidueField A))).toProjective.Equation
          (algebraMap A (IsLocalRing.ResidueField A) ∘ N.coords) :=
    hIntegralEq.map (algebraMap A (IsLocalRing.ResidueField A))
  rw [A.residue_extendedIntegralModel_eq R k E hA] at hReducedEq
  rw [A.residueRepresentative_of_ne_zero P hP]
  change ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.Equation
    (fun i ↦ algebraMap A (IsLocalRing.ResidueField A)
      ((A.unitCoordinateNormalization P hP).coords i))
  simpa [Function.comp_def, N] using hReducedEq

/-- Under good reduction, the reduced representative is a nonsingular projective point. -/
theorem residueRepresentative_nonsingular (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (P : Fin 3 → ksep) (hP : P ≠ 0)
    (hEq : (E.map (algebraMap k ksep)).toProjective.Equation P) :
    ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.Nonsingular
      (A.residueRepresentative P) := by
  letI : (E.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction (R := R) (W := E)).mp
      (inferInstance : E.HasGoodReduction R)
  exact WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero
    (A.residueRepresentative_equation R k E hA P hP hEq)
    (A.residueRepresentative_ne_zero P hP)

/-- Projective residue reduction sends every nonsingular projective point to a nonsingular point
on the reduced curve. -/
theorem projectiveResidue_nonsingularLift (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (P : (E.map (algebraMap k ksep)).toProjective.Point) :
    ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.NonsingularLift
      (A.projectiveResidue P.point) := by
  rcases P with @⟨P, hP⟩
  revert hP
  refine P.inductionOn ?_
  intro p hp
  rw [A.projectiveResidue_mk]
  exact A.residueRepresentative_nonsingular R k E hA p hp.ne_zero hp.left

/-- The total specialization map from separable-closure points to points on the reduced curve. -/
noncomputable def pointSpecialization (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    (E.map (algebraMap k ksep)).toAffine.Point →
      ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.Point :=
  fun P ↦ ⟨A.projectiveResidue_nonsingularLift R k E hA P.toProjective⟩

/-- An affine prime-to-residue-characteristic torsion point has integral coordinates. -/
theorem exists_integral_affine_coords_of_torsion
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] [DecidableEq ksep]
    {x y : ksep}
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular x y)
    (htor : WeierstrassCurve.Affine.Point.some x y hxy ∈
      AddSubgroup.torsionBy (E.map (algebraMap k ksep)).toAffine.Point (n : ℤ)) :
    ∃ xA yA : A, (xA : ksep) = x ∧ (yA : ksep) = y := by
  let W := A.extendedIntegralModel R k E hA
  have hnR : (n : IsLocalRing.ResidueField R) ≠ 0 := NeZero.ne _
  have hnbar : (n : IsLocalRing.ResidueField A) ≠ 0 := by
    intro hn0
    apply hnR
    apply (A.baseResidueMap R k hA).injective
    simpa using hn0
  have hunitn : IsUnit (n : A) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).mp
    simpa using hnbar
  have hnAInt : ((n : ℤ) : A) ≠ 0 := by
    exact_mod_cast hunitn.ne_zero
  have hnsep : ((n : ℤ) : ksep) ≠ 0 := by
    intro hn0
    apply hnAInt
    apply A.subtype_injective
    simpa using hn0
  have hnsmul : n • (WeierstrassCurve.Affine.Point.some x y hxy :
      (E.map (algebraMap k ksep)).toAffine.Point) = 0 :=
    AddSubgroup.torsionBy.nsmul_iff.mp htor
  have hzsmul : (n : ℤ) •
      (WeierstrassCurve.Affine.Point.some x y hxy :
        (E.map (algebraMap k ksep)).toAffine.Point) = 0 := by
    simpa using hnsmul
  have hpsi : ((E.map (algebraMap k ksep)).ΨSq (n : ℤ)).eval x = 0 :=
    (FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero
      (E.map (algebraMap k ksep)) hxy).mpr hzsmul
  have hroot : ((W.ΨSq (n : ℤ)).map A.subtype).IsRoot x := by
    rw [Polynomial.IsRoot.def, ← W.map_ΨSq, A.map_extendedIntegralModel_eq R k E hA]
    exact hpsi
  have hlc : IsUnit (W.ΨSq (n : ℤ)).leadingCoeff := by
    rw [W.leadingCoeff_ΨSq hnAInt]
    exact (by simpa using hunitn.pow 2)
  obtain ⟨xA, hxA⟩ := Polynomial.exists_lift_of_isRoot_of_isUnit_leadingCoeff hlc hroot
  have hxA' : A.subtype xA = x := by simpa using hxA
  have hEq : (W.map (algebraMap A ksep)).toAffine.Equation
      (algebraMap A ksep xA) y := by
    rw [show algebraMap A ksep = A.subtype from rfl,
      A.map_extendedIntegralModel_eq R k E hA]
    rw [hxA']
    exact hxy.left
  obtain ⟨yA, hyA⟩ := WeierstrassCurve.exists_integral_y_of_equation W hEq
  exact ⟨xA, yA, hxA, hyA⟩

/-- The integral x-coordinate of an affine `n`-torsion point lies on the exact squarefree-factor
support of `ΨSq n`. -/
theorem torsion_x_isRoot_prePsi_or_even_and_psiTwoSq
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (n : ℕ) [DecidableEq ksep]
    {x y : ksep}
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular x y)
    (htor : WeierstrassCurve.Affine.Point.some x y hxy ∈
      AddSubgroup.torsionBy (E.map (algebraMap k ksep)).toAffine.Point (n : ℤ))
    (xA : A) (hxA : (xA : ksep) = x) :
    ((A.extendedIntegralModel R k E hA).preΨ' n).IsRoot xA ∨
      Even n ∧ (A.extendedIntegralModel R k E hA).Ψ₂Sq.IsRoot xA := by
  let W := A.extendedIntegralModel R k E hA
  have hnsmul : n • (WeierstrassCurve.Affine.Point.some x y hxy :
      (E.map (algebraMap k ksep)).toAffine.Point) = 0 :=
    AddSubgroup.torsionBy.nsmul_iff.mp htor
  have hzsmul : (n : ℤ) •
      (WeierstrassCurve.Affine.Point.some x y hxy :
        (E.map (algebraMap k ksep)).toAffine.Point) = 0 := by
    simpa using hnsmul
  have hpsi : ((E.map (algebraMap k ksep)).ΨSq (n : ℤ)).eval x = 0 :=
    (FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero
      (E.map (algebraMap k ksep)) hxy).mpr hzsmul
  have hrootMap : ((W.ΨSq (n : ℤ)).map A.subtype).IsRoot x := by
    rw [Polynomial.IsRoot.def, ← W.map_ΨSq, A.map_extendedIntegralModel_eq R k E hA]
    exact hpsi
  have hroot : (W.ΨSq (n : ℤ)).IsRoot xA := by
    rw [Polynomial.IsRoot.def] at hrootMap ⊢
    apply A.subtype_injective
    rw [map_zero, ← Polynomial.eval_map_apply, show A.subtype xA = x from hxA]
    exact hrootMap
  exact W.prePsi_isRoot_or_even_and_psiTwoSq_isRoot_of_psiSq_isRoot hroot

/-- Two integral affine torsion x-coordinates with the same residue are equal.  In the even case
the `Ψ₂Sq` factor is used only after nonvanishing of `n` forces residue characteristic different
from two. -/
theorem torsion_x_eq_of_residue_eq
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] [DecidableEq ksep]
    {x₁ y₁ x₂ y₂ : ksep}
    (h₁ : (E.map (algebraMap k ksep)).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E.map (algebraMap k ksep)).toAffine.Nonsingular x₂ y₂)
    (htor₁ : WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ∈
      AddSubgroup.torsionBy (E.map (algebraMap k ksep)).toAffine.Point (n : ℤ))
    (htor₂ : WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ ∈
      AddSubgroup.torsionBy (E.map (algebraMap k ksep)).toAffine.Point (n : ℤ))
    (xA₁ xA₂ : A) (hxA₁ : (xA₁ : ksep) = x₁) (hxA₂ : (xA₂ : ksep) = x₂)
    (hbar : algebraMap A (IsLocalRing.ResidueField A) xA₁ =
      algebraMap A (IsLocalRing.ResidueField A) xA₂) :
    xA₁ = xA₂ := by
  classical
  let κA := IsLocalRing.ResidueField A
  let ρ : A →+* κA := algebraMap A κA
  let W := A.extendedIntegralModel R k E hA
  let Ebar := (E.reduction R).map (A.baseResidueMap R k hA)
  letI : (E.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction (R := R) (W := E)).mp
      (inferInstance : E.HasGoodReduction R)
  letI : Ebar.IsElliptic := by
    dsimp only [Ebar]
    infer_instance
  have hnR : (n : IsLocalRing.ResidueField R) ≠ 0 := NeZero.ne _
  have hnbar : (n : κA) ≠ 0 := by
    intro hn0
    apply hnR
    apply (A.baseResidueMap R k hA).injective
    simpa [κA] using hn0
  have hmodel : W.map ρ = Ebar := by
    simpa [W, ρ, κA, Ebar] using A.residue_extendedIntegralModel_eq R k E hA
  have hpsep : ((W.preΨ' n).map ρ).Separable := by
    rw [← W.map_preΨ', hmodel]
    exact FLT.EllipticCurve.TorsionProvider.prePsi_separable Ebar hnbar
  have hcop : ∀ z : κA, ((W.preΨ' n).map ρ).eval z = 0 →
      ((W.Ψ₂Sq).map ρ).eval z ≠ 0 := by
    rw [← W.map_preΨ', ← W.map_Ψ₂Sq, hmodel]
    exact FLTMethodology.Torsion.prePsi_pointwise_coprime Ebar hnbar
  have hfactor₁ := A.torsion_x_isRoot_prePsi_or_even_and_psiTwoSq
    R k E hA n h₁ htor₁ xA₁ hxA₁
  have hfactor₂ := A.torsion_x_isRoot_prePsi_or_even_and_psiTwoSq
    R k E hA n h₂ htor₂ xA₂ hxA₂
  change (W.preΨ' n).IsRoot xA₁ ∨ Even n ∧ W.Ψ₂Sq.IsRoot xA₁ at hfactor₁
  change (W.preΨ' n).IsRoot xA₂ ∨ Even n ∧ W.Ψ₂Sq.IsRoot xA₂ at hfactor₂
  rcases hfactor₁ with hpre₁ | ⟨heven, htwo₁⟩ <;>
    rcases hfactor₂ with hpre₂ | ⟨heven', htwo₂⟩
  · exact Polynomial.roots_eq_of_same_map ρ hpsep hpre₁ hpre₂ hbar
  · exfalso
    apply hcop (ρ xA₁)
    · simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using congrArg ρ hpre₁
    · rw [hbar]
      simpa [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_at_apply, ρ, κA]
        using congrArg ρ htwo₂
  · exfalso
    apply hcop (ρ xA₂)
    · simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using congrArg ρ hpre₂
    · rw [← hbar]
      simpa [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_at_apply, ρ, κA]
        using congrArg ρ htwo₁
  · have htwoChar : (2 : κA) ≠ 0 := by
      intro hzero
      rcases heven with ⟨m, rfl⟩
      apply hnbar
      rw [Nat.cast_add]
      calc
        (m : κA) + (m : κA) = (2 : κA) * (m : κA) := by ring
        _ = 0 := by rw [hzero, zero_mul]
    have hqsep : (W.Ψ₂Sq.map ρ).Separable := by
      rw [← W.map_Ψ₂Sq, hmodel]
      exact FLTMethodology.Torsion.psiTwoSq_separable Ebar htwoChar
    exact Polynomial.roots_eq_of_same_map ρ hqsep htwo₁ htwo₂ hbar

/-- Specialization of an integral affine point is coordinatewise reduction. -/
theorem pointSpecialization_some_point_eq_integral
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (xA yA : A)
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular
      (xA : ksep) (yA : ksep)) :
    (A.pointSpecialization R k E hA
      (WeierstrassCurve.Affine.Point.some (xA : ksep) (yA : ksep) hxy)).point =
      (⟦A.residueVector ![xA, yA, 1]⟧ :
        WeierstrassCurve.Projective.PointClass (IsLocalRing.ResidueField A)) := by
  change A.projectiveResidue ⟦![(xA : ksep), (yA : ksep), 1]⟧ = _
  rw [show (![(xA : ksep), (yA : ksep), 1] : Fin 3 → ksep) =
      (fun i => ((![xA, yA, 1] : Fin 3 → A) i : ksep)) by
        funext i
        fin_cases i <;> rfl]
  exact A.projectiveResidue_mk_integral ![xA, yA, 1] ⟨2, isUnit_one⟩

/-- The point at infinity specializes to the point at infinity. -/
theorem pointSpecialization_zero_point_eq
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    (A.pointSpecialization R k E hA 0).point =
      (⟦![0, 1, 0]⟧ :
        WeierstrassCurve.Projective.PointClass (IsLocalRing.ResidueField A)) := by
  change A.projectiveResidue (0 :
    (E.map (algebraMap k ksep)).toProjective.Point).point = _
  rw [WeierstrassCurve.Projective.Point.zero_point]
  rw [show (![0, 1, 0] : Fin 3 → ksep) =
      (fun i => ((![0, 1, 0] : Fin 3 → A) i : ksep)) by
        funext i
        fin_cases i <;> rfl]
  rw [A.projectiveResidue_mk_integral ![(0 : A), 1, 0] ⟨1, isUnit_one⟩]
  congr 1
  funext i
  fin_cases i <;> simp [ValuationSubring.residueVector]

@[simp]
theorem pointSpecialization_zero_eq
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    A.pointSpecialization R k E hA 0 = 0 := by
  apply WeierstrassCurve.Projective.Point.ext
  rw [A.pointSpecialization_zero_point_eq R k E hA,
    WeierstrassCurve.Projective.Point.zero_point]

/-- An integral affine point cannot specialize to the point at infinity. -/
theorem pointSpecialization_some_ne_zero_of_integral
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (xA yA : A)
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular
      (xA : ksep) (yA : ksep)) :
    A.pointSpecialization R k E hA
      (WeierstrassCurve.Affine.Point.some (xA : ksep) (yA : ksep) hxy) ≠ 0 := by
  intro hzero
  have hpoint := congrArg (fun P => P.point) hzero
  rw [A.pointSpecialization_some_point_eq_integral R k E hA xA yA hxy,
    WeierstrassCurve.Projective.Point.zero_point] at hpoint
  have hequiv : A.residueVector ![xA, yA, 1] ≈
      (![0, 1, 0] : Fin 3 → IsLocalRing.ResidueField A) := Quotient.eq.mp hpoint
  exact WeierstrassCurve.Projective.not_equiv_of_Z_eq_zero_right
    (by simp [ValuationSubring.residueVector]) (by simp) hequiv

/-- Specialization is injective on prime-to-residue-characteristic torsion. -/
theorem pointSpecialization_injOn_torsion
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R] [DecidableEq ksep]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] :
    Set.InjOn (A.pointSpecialization R k E hA)
      (AddSubgroup.torsionBy (E.map (algebraMap k ksep)).toAffine.Point (n : ℤ)) := by
  classical
  intro P hP Q hQ hPQ
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x₂ y₂ h₂ =>
          obtain ⟨xA₂, yA₂, hxA₂, hyA₂⟩ :=
            A.exists_integral_affine_coords_of_torsion R k E hA n h₂ hQ
          subst x₂
          subst y₂
          exfalso
          exact A.pointSpecialization_some_ne_zero_of_integral R k E hA xA₂ yA₂ h₂
            (hPQ.symm.trans (A.pointSpecialization_zero_eq R k E hA))
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          obtain ⟨xA₁, yA₁, hxA₁, hyA₁⟩ :=
            A.exists_integral_affine_coords_of_torsion R k E hA n h₁ hP
          subst x₁
          subst y₁
          exfalso
          exact A.pointSpecialization_some_ne_zero_of_integral R k E hA xA₁ yA₁ h₁
            (hPQ.trans (A.pointSpecialization_zero_eq R k E hA))
      | some x₂ y₂ h₂ =>
          obtain ⟨xA₁, yA₁, hxA₁, hyA₁⟩ :=
            A.exists_integral_affine_coords_of_torsion R k E hA n h₁ hP
          obtain ⟨xA₂, yA₂, hxA₂, hyA₂⟩ :=
            A.exists_integral_affine_coords_of_torsion R k E hA n h₂ hQ
          subst x₁
          subst y₁
          subst x₂
          subst y₂
          have hpoint := congrArg (fun T => T.point) hPQ
          rw [A.pointSpecialization_some_point_eq_integral R k E hA xA₁ yA₁ h₁,
            A.pointSpecialization_some_point_eq_integral R k E hA xA₂ yA₂ h₂] at hpoint
          have hres := A.residue_affine_coords_eq_of_projectiveResidue_eq
            xA₁ yA₁ xA₂ yA₂ (by
              rw [A.projectiveResidue_mk_integral ![xA₁, yA₁, 1] ⟨2, isUnit_one⟩,
                A.projectiveResidue_mk_integral ![xA₂, yA₂, 1] ⟨2, isUnit_one⟩]
              exact hpoint)
          have hxA : xA₁ = xA₂ := A.torsion_x_eq_of_residue_eq R k E hA n
            h₁ h₂ hP hQ xA₁ xA₂ rfl rfl hres.1
          have hxRep :
              (WeierstrassCurve.Affine.Point.some (xA₁ : ksep) (yA₁ : ksep) h₁).xRep =
                (WeierstrassCurve.Affine.Point.some
                  (xA₂ : ksep) (yA₂ : ksep) h₂).xRep := by
            simp [hxA]
          rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxRep with
            heq | hneg
          · exact heq
          · let κA := IsLocalRing.ResidueField A
            let ρ : A →+* κA := algebraMap A κA
            let W := A.extendedIntegralModel R k E hA
            let Ebar := (E.reduction R).map (A.baseResidueMap R k hA)
            letI : (E.reduction R).IsElliptic :=
              (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
                (R := R) (W := E)).mp (inferInstance : E.HasGoodReduction R)
            letI : Ebar.IsElliptic := by
              dsimp only [Ebar]
              infer_instance
            have hmodel : W.map ρ = Ebar := by
              simpa [W, ρ, κA, Ebar] using
                A.residue_extendedIntegralModel_eq R k E hA
            have hnR : (n : IsLocalRing.ResidueField R) ≠ 0 := NeZero.ne _
            have hnbar : (n : κA) ≠ 0 := by
              intro hn0
              apply hnR
              apply (A.baseResidueMap R k hA).injective
              simpa [κA] using hn0
            have hcurve : W.map A.subtype = E.map (algebraMap k ksep) := by
              simpa [W] using A.map_extendedIntegralModel_eq R k E hA
            have ha₁ : A.subtype W.a₁ = (E.map (algebraMap k ksep)).a₁ := by
              simpa using congrArg WeierstrassCurve.a₁ hcurve
            have ha₃ : A.subtype W.a₃ = (E.map (algebraMap k ksep)).a₃ := by
              simpa using congrArg WeierstrassCurve.a₃ hcurve
            have hnegCoords :
                (xA₁ : ksep) = (xA₂ : ksep) ∧
                  (yA₁ : ksep) =
                    (E.map (algebraMap k ksep)).toAffine.negY
                      (xA₂ : ksep) (yA₂ : ksep) := by
              simpa only [WeierstrassCurve.Affine.Point.neg_some,
                WeierstrassCurve.Affine.Point.some.injEq] using hneg
            have hnegY :
                (yA₁ : ksep) = -(yA₂ : ksep) -
                  (E.map (algebraMap k ksep)).a₁ * (xA₂ : ksep) -
                    (E.map (algebraMap k ksep)).a₃ := by
              simpa only [WeierstrassCurve.Affine.negY] using hnegCoords.2
            have hyAneg : yA₁ = W.toAffine.negY xA₂ yA₂ := by
              apply A.subtype_injective
              change A.subtype yA₁ = -A.subtype yA₂ -
                A.subtype W.a₁ * A.subtype xA₂ - A.subtype W.a₃
              rw [ha₁, ha₃]
              exact hnegY
            have hybarneg := congrArg ρ hyAneg
            have hgap :
                2 * ρ yA₁ + ρ W.a₁ * ρ xA₁ + ρ W.a₃ = 0 := by
              simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul]
                at hybarneg
              linear_combination hres.2 + hybarneg +
                ρ W.a₁ * congrArg ρ hxA
            have hEqMap : (W.map A.subtype).toAffine.Equation
                (xA₁ : ksep) (yA₁ : ksep) := by
              rw [hcurve]
              exact h₁.left
            have hEqA : W.toAffine.Equation xA₁ yA₁ :=
              (W.toAffine.map_equation A.subtype_injective xA₁ yA₁).mp hEqMap
            have hEqBar : (W.map ρ).toAffine.Equation (ρ xA₁) (ρ yA₁) :=
              hEqA.map ρ
            have hgap' :
                2 * ρ yA₁ + (W.map ρ).a₁ * ρ xA₁ + (W.map ρ).a₃ = 0 := by
              simpa using hgap
            have htwoBar : (W.map ρ).Ψ₂Sq.eval (ρ xA₁) = 0 := by
              rw [WeierstrassCurve.psiTwoSq_eval_eq_negationGap_sq
                (W.map ρ) hEqBar, hgap', zero_pow (by norm_num)]
            have hfactor := A.torsion_x_isRoot_prePsi_or_even_and_psiTwoSq
              R k E hA n h₁ hP xA₁ rfl
            change (W.preΨ' n).IsRoot xA₁ ∨
              Even n ∧ W.Ψ₂Sq.IsRoot xA₁ at hfactor
            rcases hfactor with hpre | ⟨_, htwo⟩
            · have hpreBar : (Ebar.preΨ' n).eval (ρ xA₁) = 0 := by
                rw [← hmodel, W.map_preΨ']
                simpa [Polynomial.IsRoot.def, Polynomial.eval_map,
                  Polynomial.eval₂_at_apply, ρ, κA] using congrArg ρ hpre
              have htwoBar' : Ebar.Ψ₂Sq.eval (ρ xA₁) = 0 := by
                rw [← hmodel]
                exact htwoBar
              exact ((FLTMethodology.Torsion.prePsi_pointwise_coprime
                Ebar hnbar (ρ xA₁) hpreBar) htwoBar').elim
            · have htwoMap : ((W.Ψ₂Sq).map A.subtype).IsRoot (xA₁ : ksep) := by
                rw [Polynomial.IsRoot.def] at htwo ⊢
                change (W.Ψ₂Sq.map A.subtype).eval (A.subtype xA₁) = 0
                rw [Polynomial.eval_map_apply, htwo, map_zero]
              have htwoSource :
                  (E.map (algebraMap k ksep)).Ψ₂Sq.IsRoot (xA₁ : ksep) := by
                rw [← hcurve, W.map_Ψ₂Sq]
                exact htwoMap
              have hpsiTwo :
                  ((E.map (algebraMap k ksep)).ΨSq (2 : ℤ)).eval (xA₁ : ksep) = 0 := by
                rw [(E.map (algebraMap k ksep)).ΨSq_two]
                exact htwoSource
              have htwoP : (2 : ℤ) •
                  (WeierstrassCurve.Affine.Point.some
                    (xA₁ : ksep) (yA₁ : ksep) h₁ :
                    (E.map (algebraMap k ksep)).toAffine.Point) = 0 :=
                (FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero
                  (E.map (algebraMap k ksep)) h₁).mp hpsiTwo
              have hself :
                  WeierstrassCurve.Affine.Point.some
                      (xA₁ : ksep) (yA₁ : ksep) h₁ =
                    -WeierstrassCurve.Affine.Point.some
                      (xA₁ : ksep) (yA₁ : ksep) h₁ := by
                rw [eq_neg_iff_add_eq_zero, ← two_zsmul]
                exact htwoP
              have hminus :
                  -WeierstrassCurve.Affine.Point.some
                      (xA₁ : ksep) (yA₁ : ksep) h₁ =
                    WeierstrassCurve.Affine.Point.some
                      (xA₂ : ksep) (yA₂ : ksep) h₂ := by
                calc
                  -WeierstrassCurve.Affine.Point.some
                      (xA₁ : ksep) (yA₁ : ksep) h₁ =
                    -(-WeierstrassCurve.Affine.Point.some
                      (xA₂ : ksep) (yA₂ : ksep) h₂) := congrArg Neg.neg hneg
                  _ = WeierstrassCurve.Affine.Point.some
                      (xA₂ : ksep) (yA₂ : ksep) h₂ := neg_neg _
              exact hself.trans hminus

/-- The total point-specialization map is invariant under inertia. -/
theorem pointSpecialization_inertia (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R] [DecidableEq ksep]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (P : (E.map (algebraMap k ksep)).toAffine.Point) :
    A.pointSpecialization R k E hA
        (WeierstrassCurve.Affine.Point.map (W' := E) σ.1.toAlgHom P) =
      A.pointSpecialization R k E hA P := by
  apply WeierstrassCurve.Projective.Point.ext
  cases P with
  | zero => rfl
  | some x y h =>
      change A.projectiveResidue ⟦![σ • x, σ • y, 1]⟧ =
        A.projectiveResidue ⟦![x, y, 1]⟧
      rw [A.projectiveResidue_mk, A.projectiveResidue_mk]
      rw [show ![σ • x, σ • y, 1] = (fun i ↦ σ • ![x, y, 1] i) by
        funext i
        fin_cases i <;> simp]
      exact A.projectiveResidue_inertia k σ hσ ![x, y, 1]

end PointSpecialization

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
  WeierstrassCurve.torsion_fixed_of_invariant_injective E n
    (fun σ : 𝒪.decompositionSubgroup k => (σ : ksep ≃ₐ[k] ksep))
    (𝒪.inertiaSubgroup k)
    (𝒪.pointSpecialization R k E h𝒪)
    (𝒪.pointSpecialization_injOn_torsion R k E h𝒪 n)
    (fun σ hσ P _ => 𝒪.pointSpecialization_inertia R k E h𝒪 σ hσ P)
