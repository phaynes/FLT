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
  sorry
