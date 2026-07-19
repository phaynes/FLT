/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Deformations.RepresentationTheory.Frobenius
public import FLT.Deformations.RepresentationTheory.IntegralClosure
public import FLT.Mathlib.FieldTheory.Galois.Infinite
public import FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

import FLT.NumberField.Completion.Finite
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Functoriality of the absolute Galois group

For a field extension `K → L`, we define the induced map between absolute
Galois groups `Γ L → Γ K` and prove its continuity, together with finite-index
results for fixing subgroups.
-/

@[expose] public section

variable {K L : Type*} [Field K] [Field L]
variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inertia subgroup of a discrete additive action is closed. -/
theorem AddSubgroup.isClosed_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M)
    (G : Type*) [Group G] [TopologicalSpace G] [MulAction G M] [ContinuousSMulDiscrete G M] :
    IsClosed (I.inertia G : Set G) := by
  have h : (I.inertia G : Set G) = ⋂ x : M, {σ : G | σ • x - x ∈ I} := by
    ext σ
    simp [AddSubgroup.mem_inertia]
  rw [h]
  refine isClosed_iInter fun x ↦ ?_
  have hopen : ∀ S : Set M, IsOpen {σ : G | σ • x ∈ S} := fun S ↦ by
    have : {σ : G | σ • x ∈ S} = ⋃ y ∈ S, {σ : G | σ • x = y} := by
      ext σ
      simp
    rw [this]
    exact isOpen_biUnion fun y _ ↦ ContinuousSMulDiscrete.isOpen_smul_eq G x y
  rw [show {σ : G | σ • x - x ∈ I} = {σ : G | σ • x ∈ {y | y - x ∈ I}} from rfl,
    ← isOpen_compl_iff]
  exact hopen {y | y - x ∈ I}ᶜ

open NumberField

variable [NumberField K]

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option backward.isDefEq.respectTransparency false in
/-- Given a field extension, this is a map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.mapAux (f : K →+* L) : Γ L →* Γ K where
  toFun σ :=
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    ((σ.restrictScalars K).toAlgHom.comp
      (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ)).restrictNormal' (Kᵃˡᵍ)
  map_one' := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans (by simp)
  map_mul' σ₁ σ₂ := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (AlgebraicClosure.map f).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans ?_
    refine ((AlgHom.restrictNormal_commutes _ _ _).trans ?_).symm
    simpa [absoluteGaloisGroup] using! AlgHom.restrictNormal_commutes _ _ _

/-- Given a field extension, this is a continuous map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.map (f : K →+* L) : Γ L →ₜ* Γ K where
  __ := Field.absoluteGaloisGroup.mapAux f
  continuous_toFun := by
    classical
    letI := f.toAlgebra
    let F : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ := IsAlgClosed.lift
    letI := F.toRingHom.toAlgebra
    apply continuous_of_continuousAt_one (Field.absoluteGaloisGroup.mapAux f)
    rw [ContinuousAt, map_one]
    refine ((galGroupBasis L (Lᵃˡᵍ)).nhds_one_hasBasis.tendsto_iff
      (galGroupBasis K (Kᵃˡᵍ)).nhds_one_hasBasis).mpr ?_
    rintro _ ⟨_, ⟨K', hK', rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨.adjoin _ (K'.map F), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
    · have : FiniteDimensional _ _ := hK'
      obtain ⟨s, hs⟩ := K'.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType K K'))
      obtain rfl := IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
      simp only [IntermediateField.adjoin_map, IntermediateField.adjoin_adjoin_right,
        ← Finset.coe_image]
      refine IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
    · exact F.injective ((AlgHom.restrictNormal_commutes _ _ _).trans
        (hσ ⟨F x, IntermediateField.subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩))

set_option allowUnsafeReducibility true in
attribute [reducible] Field.absoluteGaloisGroup -- lol WTF is going on here

set_option backward.isDefEq.respectTransparency false in
lemma Field.absoluteGaloisGroup.lift_map (f : K →+* L) (σ : Γ L) (x : Kᵃˡᵍ) :
    AlgebraicClosure.map f (map f σ x) = σ (AlgebraicClosure.map f x) := by
  letI := f.toAlgebra
  letI := (AlgebraicClosure.map f).toAlgebra
  exact AlgHom.restrictNormal_commutes _ _ _


attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

attribute [local instance] Valued.toNormedField in
lemma isIntegral_of_spectralNorm_le_one
    {K L Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Field K] [Field L]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] [Algebra K L] [Algebra.IsAlgebraic K L]
    {x : L} (hx : spectralNorm K L x ≤ 1) : IsIntegral (Valued.v : Valuation K Γ₀).integer x := by
  have : minpoly K x ∈ Polynomial.lifts (Valued.v : Valuation K Γ₀).integer.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at this
    split_ifs at this with h
    · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly K x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at this
      simpa [Valuation.mem_integer_iff] using this
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · simp [← h, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, one_mem]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_mem]
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic this
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K,
    Subring.algebraMap_def, hP, minpoly.aeval]

lemma spectralNorm_inv
    {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L (x⁻¹) = (spectralNorm K L x)⁻¹ := by
  by_cases H : x = 0
  · simp [H, spectralNorm_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← spectralAlgNorm_def, ← spectralAlgNorm_def, ← spectralAlgNorm_mul (K := K) x x⁻¹,
    mul_inv_cancel₀ H, spectralAlgNorm_one]

noncomputable instance : NontriviallyNormedField Kᵥ := Valued.toNontriviallyNormedField _ _

instance valuationRing_integralClosure
    {L : Type*} [Field L] [Algebra Kᵥ L] [Algebra.IsAlgebraic Kᵥ L] :
    ValuationRing (IntegralClosure 𝒪ᵥ L) := by
  refine ValuationSubring.instValuationRingSubtypeMem ⟨(integralClosure 𝒪ᵥ L).toSubring, ?_⟩
  intro x
  obtain hx | hx := le_total (spectralNorm Kᵥ L x) 1
  · exact .inl (isIntegral_of_spectralNorm_le_one hx)
  · have := inv_le_one_of_one_le₀ hx
    rw [← spectralNorm_inv] at this
    exact .inr (isIntegral_of_spectralNorm_le_one this)

/-- The local inertia subgroup of a number field at a prime, defined as a subgroup
of the local galois group. -/
noncomputable
def localInertiaGroup : Subgroup (Γ Kᵥ) :=
  (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).toAddSubgroup.inertia (Γ Kᵥ)

/-- The local inertia subgroup at a finite place is closed. -/
theorem isClosed_localInertiaGroup :
    IsClosed (localInertiaGroup v : Set (Γ Kᵥ)) :=
  AddSubgroup.isClosed_inertia _ _

open IntermediateField in
/-- The subgroup of the local galois group which is the kernel of the canonical map `Iᵥ → k(v)ˣ`.
Note that this definition is somewhat cheating, abusing the fact that the field corresponding
to this subgroup is `Kᵘʳ(ᵖ⁻¹√ϖ)` (where `p` is `#k(v)` and not the characteristic)
and that all units in `Kᵘʳ` have `p-1`-th roots.

TODO: show that this is indeed the right group. -/
noncomputable
def localTameAbelianInertiaGroup : Subgroup (Γ Kᵥ) where
  carrier := { σ | ∀ x, x ^ (Nat.card (κ 𝒪ᵥ) - 1) ∈ fixedField (localInertiaGroup v) → σ x = x }
  mul_mem' {σ τ} hσ hτ x hx := by dsimp; rw [hτ x hx, hσ x hx]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ x hx := by
    conv_lhs => rw [← hσ x hx]
    simp [AlgEquiv.aut_inv]

instance : CharZero Kᵥ :=
  ((algebraMap K Kᵥ).charZero_iff (algebraMap K Kᵥ).injective).mp inferInstance

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

/-- The repository's tame-abelian inertia proxy is contained in local inertia.

Identifying this proxy with the kernel of the tame residue character is a separate arithmetic
theorem. -/
theorem localTameAbelianInertiaGroup_le_localInertiaGroup :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v := by
  intro σ hσ
  have hfix : σ ∈ (IntermediateField.fixedField (localInertiaGroup v)).fixingSubgroup := by
    rintro ⟨x, hx⟩
    exact hσ x (pow_mem hx _)
  rwa [InfiniteGalois.fixingSubgroup_fixedField
    ⟨localInertiaGroup v, isClosed_localInertiaGroup v⟩] at hfix

instance : Finite (IsLocalRing.ResidueField 𝒪ᵥ) := inferInstance

instance finite_adicCompletionIntegers_quotient
    {I : Ideal 𝒪ᵥ} [I.IsPrime] [NeZero I] : Finite (𝒪ᵥ ⧸ I) := by
  obtain rfl := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime 𝒪ᵥ).mp
      inferInstance).2.unique ⟨NeZero.ne _, ‹I.IsPrime›⟩ ⟨IsDiscreteValuationRing.not_a_field 𝒪ᵥ,
      inferInstanceAs (𝔪 _).IsPrime⟩
  exact inferInstanceAs <| Finite (IsLocalRing.ResidueField _)

instance neZero_maximalIdeal_integralClosure :
    NeZero (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) := by
  have : 𝒪ᵥ ≠ ⊤ := by
    refine fun h ↦ IsDiscreteValuationRing.not_isField 𝒪ᵥ (h ▸ ?_)
    exact (Subring.topEquiv (R := Kᵥ)).isField (Semifield.toIsField Kᵥ)
  exact ⟨(Ideal.bot_lt_of_maximal (𝔪 _)
    (not_isField_integralClosure (L := Kᵥᵃˡᵍ) _ this)).ne'⟩

/-- The residue-field unit exponent is a unit in the integral closure at a finite place. -/
theorem isUnit_card_sub_one_ICv :
    IsUnit
      (((Nat.card (κ 𝒪ᵥ) - 1 : ℕ) : IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) := by
  have hbase : IsUnit (((Nat.card (κ 𝒪ᵥ) - 1 : ℕ) : 𝒪ᵥ)) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    letI := Fintype.ofFinite (κ 𝒪ᵥ)
    rw [map_natCast]
    rw [Nat.cast_sub (Finite.one_lt_card (α := κ 𝒪ᵥ)).le]
    simp [Nat.card_eq_fintype_card]
  simpa only [map_natCast] using
    hbase.map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

/-- The units of the base residue field are the `(q - 1)`-st roots of unity in the residue field
of the integral closure. This is residue-field descent, not Henselian lifting. -/
noncomputable def residueUnitsEquivRootsOfUnity_at_place :
    (κ 𝒪ᵥ)ˣ ≃*
      rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1) (κ (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :=
  finiteFieldUnitsEquivRootsOfUnity _ _
    (IsLocalRing.ResidueField.map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))))
    (IsLocalRing.ResidueField.map
      (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))).injective

/-- Reduction of tame roots of unity to units of the base residue field. -/
noncomputable def tameRootsReduction_at_place :
    rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) →* (κ 𝒪ᵥ)ˣ :=
  (residueUnitsEquivRootsOfUnity_at_place v).symm.toMonoidHom.comp
    (restrictRootsOfUnity (IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
      (Nat.card (κ 𝒪ᵥ) - 1))

/-- Reduction of tame roots of unity at a finite place is injective. -/
theorem tameRootsReduction_at_place_injective :
    Function.Injective (tameRootsReduction_at_place v) :=
  (residueUnitsEquivRootsOfUnity_at_place v).symm.injective.comp
    (rootsOfUnity_residue_injective (isUnit_card_sub_one_ICv v))

/-- Every root of unity in the algebraic closure is integral, so passing to the integral closure
does not change the group of `n`-th roots of unity. -/
noncomputable def integralClosureRootsEquiv (n : ℕ) [NeZero n] :
    rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) ≃*
      rootsOfUnity n (Kᵥᵃˡᵍ) := by
  let f := restrictRootsOfUnity
    (algebraMap (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) (Kᵥᵃˡᵍ)) n
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply rootsOfUnity.coe_injective
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n (Kᵥᵃˡᵍ) =>
      ((z : (Kᵥᵃˡᵍ)ˣ) : Kᵥᵃˡᵍ)) hxy
  · intro z
    have hzpow : (((z : (Kᵥᵃˡᵍ)ˣ) : Kᵥᵃˡᵍ)) ^ n = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val ((mem_rootsOfUnity n _).mp z.prop)
    have hzint : IsIntegral 𝒪ᵥ (((z : (Kᵥᵃˡᵍ)ˣ) : Kᵥᵃˡᵍ)) :=
      IsIntegral.of_pow (NeZero.pos n) (hzpow ▸ isIntegral_one)
    let zi : IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ) :=
      ⟨((z : (Kᵥᵃˡᵍ)ˣ) : Kᵥᵃˡᵍ), hzint⟩
    let ziRoot : rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :=
      rootsOfUnity.mkOfPowEq zi (by
        apply Subtype.ext
        exact hzpow)
    refine ⟨ziRoot, ?_⟩
    apply rootsOfUnity.coe_injective
    rfl

theorem integralClosure_card_rootsOfUnity (n : ℕ) [NeZero n] :
    Nat.card (rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) = n := by
  rw [Nat.card_congr (integralClosureRootsEquiv v n).toEquiv]
  have hn : (n : Kᵥ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  letI : NeZero (n : Kᵥ) := ⟨hn⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity (Kᵥᵃˡᵍ) n

/-- Reduction on the prime-to-residue-characteristic roots of unity is surjective as well as
injective. This finite-cardinality proof supplies the Teichmüller lifting direction without adding
a separate Henselian-ring interface. -/
theorem tameRootsReduction_at_place_surjective :
    Function.Surjective (tameRootsReduction_at_place v) := by
  letI : NeZero (Nat.card (κ 𝒪ᵥ) - 1) :=
    ⟨(tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ))).ne'⟩
  letI : Finite
      (rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1)
        (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :=
    Finite.of_injective (integralClosureRootsEquiv v (Nat.card (κ 𝒪ᵥ) - 1)).toFun
      (integralClosureRootsEquiv v (Nat.card (κ 𝒪ᵥ) - 1)).injective
  letI := Fintype.ofFinite
    (rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1)
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
  letI := Fintype.ofFinite (κ 𝒪ᵥ)ˣ
  have hb : Function.Bijective (tameRootsReduction_at_place v) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨
      tameRootsReduction_at_place_injective v, by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
          integralClosure_card_rootsOfUnity, Nat.card_units]⟩
  exact hb.surjective

/-- Teichmüller lifting, packaged as a multiplicative equivalence. -/
noncomputable def tameRootsReductionEquiv :
    rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) ≃*
      (κ 𝒪ᵥ)ˣ :=
  MulEquiv.ofBijective (tameRootsReduction_at_place v)
    ⟨tameRootsReduction_at_place_injective v,
      tameRootsReduction_at_place_surjective v⟩

/-- If a local Galois automorphism fixes an `n`-th power, the corresponding quotient
`σ(x) / x` is an `n`-th root of unity. This is the elementary Kummer calculation used by the
tame residue character. -/
theorem galoisRatio_pow_eq_one
    (σ : Γ Kᵥ) {x : Kᵥᵃˡᵍ} (hx : x ≠ 0) {n : ℕ}
    (hpow : σ (x ^ n) = x ^ n) :
    (σ x / x) ^ n = 1 := by
  rw [div_pow, ← map_pow, hpow, div_self (pow_ne_zero n hx)]

/-- Package the Galois ratio as an integral root of unity. Integrality follows directly from its
positive power being one; no Henselian lifting or reciprocity theorem is used here. -/
noncomputable def integralGaloisRatioRoot
    (σ : Γ Kᵥ) {x : Kᵥᵃˡᵍ} (hx : x ≠ 0) {n : ℕ} [NeZero n]
    (hpow : σ (x ^ n) = x ^ n) :
    rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) := by
  have hratio : (σ x / x) ^ n = 1 := galoisRatio_pow_eq_one v σ hx hpow
  have hintegral : IsIntegral 𝒪ᵥ (σ x / x) :=
    IsIntegral.of_pow (NeZero.pos n) (hratio ▸ isIntegral_one)
  exact rootsOfUnity.mkOfPowEq
    (⟨σ x / x, hintegral⟩ : IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) (by
      apply Subtype.ext
      exact hratio)

/-- A fixed uniformizer used to normalize the elementary tame Kummer character. -/
noncomputable def tameUniformizer : Kᵥ :=
  algebraMap K Kᵥ (v.valuation_exists_uniformizer K).choose

theorem tameUniformizer_valuation :
    Valued.v (tameUniformizer v) = Multiplicative.ofAdd (-1 : ℤ) := by
  let u := (v.valuation_exists_uniformizer K).choose
  have h : (IsDedekindDomain.HeightOneSpectrum.valuation K v) u =
      Multiplicative.ofAdd (-1 : ℤ) :=
    (v.valuation_exists_uniformizer K).choose_spec
  change Valued.v (algebraMap K Kᵥ u) = Multiplicative.ofAdd (-1 : ℤ)
  rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v u] at h

theorem tameUniformizer_ne_zero : tameUniformizer v ≠ 0 := by
  intro h
  apply_fun Valued.v at h
  rw [tameUniformizer_valuation] at h
  simp at h

/-- A chosen `(q - 1)`-st root of the fixed uniformizer in the algebraic closure. -/
noncomputable def tameKummerRoot : Kᵥᵃˡᵍ :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v))
    (tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ)))).choose

theorem tameKummerRoot_pow :
    tameKummerRoot v ^ (Nat.card (κ 𝒪ᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v) :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v))
    (tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ)))).choose_spec

theorem tameKummerRoot_ne_zero : tameKummerRoot v ≠ 0 := by
  intro h
  have hp := tameKummerRoot_pow v
  rw [h, zero_pow (tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ))).ne'] at hp
  exact (map_ne_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).mpr
    (tameUniformizer_ne_zero v) hp.symm

/-- The integral `(q - 1)`-st root of unity obtained from the Kummer ratio of an inertia
automorphism. -/
noncomputable def tameKummerRatioRoot (σ : localInertiaGroup v) :
    rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) := by
  letI : NeZero (Nat.card (κ 𝒪ᵥ) - 1) :=
    ⟨(tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ))).ne'⟩
  exact integralGaloisRatioRoot v σ.1 (tameKummerRoot_ne_zero v) (by
    rw [tameKummerRoot_pow]
    exact σ.1.commutes (tameUniformizer v))

/-- The underlying function of the tame residue character. -/
noncomputable def tameResidueCharFun (σ : localInertiaGroup v) : (κ 𝒪ᵥ)ˣ :=
  tameRootsReduction_at_place v (tameKummerRatioRoot v σ)

/-- Inertia fixes the residue of every element of the integral closure. -/
theorem localInertia_residue_smul_eq (σ : localInertiaGroup v)
    (y : IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :
    IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) (σ.1 • y) =
      IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff (σ.1 • y - y)).mpr (σ.property y)

/-- Local inertia fixes every `(q - 1)`-st root of unity in the integral closure. Reduction
commutes with the action, inertia is trivial on residue, and tame-root reduction is injective. -/
theorem localInertia_fix_tameRoot (σ : localInertiaGroup v)
    (z : rootsOfUnity (Nat.card (κ 𝒪ᵥ) - 1)
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :
    σ.1 • (((z : (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
      IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) =
      (((z : (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
        IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) := by
  let n := Nat.card (κ 𝒪ᵥ) - 1
  letI : NeZero n :=
    ⟨(tsub_pos_of_lt (Finite.one_lt_card (α := κ 𝒪ᵥ))).ne'⟩
  let y : IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ) :=
    (((z : (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
      IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))
  have hy : y ^ n = 1 := by
    simpa only [y, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val ((mem_rootsOfUnity n _).mp z.prop)
  let zσ : rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) :=
    rootsOfUnity.mkOfPowEq (σ.1 • y) (by
      apply Subtype.ext
      exact congrArg Subtype.val (by
        change (σ.1 • y) ^ n = 1
        change ((MulSemiringAction.toRingHom _ _ σ.1) y) ^ n = 1
        rw [← map_pow (MulSemiringAction.toRingHom _ _ σ.1), hy, map_one]))
  have hred : tameRootsReduction_at_place v zσ =
      tameRootsReduction_at_place v z := by
    change (residueUnitsEquivRootsOfUnity_at_place v).symm
        (restrictRootsOfUnity
          (IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) n zσ) =
      (residueUnitsEquivRootsOfUnity_at_place v).symm
        (restrictRootsOfUnity
          (IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) n z)
    apply congrArg (residueUnitsEquivRootsOfUnity_at_place v).symm
    apply rootsOfUnity.coe_injective
    simp only [restrictRootsOfUnity_coe_apply, zσ, y]
    exact localInertia_residue_smul_eq v σ _
  have hzσ : zσ = z := tameRootsReduction_at_place_injective v hred
  have hc := congrArg
    (fun w : rootsOfUnity n (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) =>
    (((w : (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
      IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) hzσ
  simp only [zσ, rootsOfUnity.coe_mkOfPowEq] at hc
  simpa only [y] using hc

/-- The Galois quotient is a crossed homomorphism before passing to inertia-invariant residue. -/
theorem galoisRatio_mul
    (σ τ : Γ Kᵥ) {x : Kᵥᵃˡᵍ} (hx : x ≠ 0) :
    (σ * τ) x / x = σ (τ x / x) * (σ x / x) := by
  rw [map_div₀]
  change σ (τ x) / x = (σ (τ x) / σ x) * (σ x / x)
  have hsx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  field_simp

theorem tameKummerRatioRoot_one : tameKummerRatioRoot v 1 = 1 := by
  apply rootsOfUnity.coe_injective
  apply Subtype.ext
  change tameKummerRoot v / tameKummerRoot v = 1
  exact div_self (tameKummerRoot_ne_zero v)

theorem tameResidueCharFun_one : tameResidueCharFun v 1 = 1 := by
  rw [tameResidueCharFun, tameKummerRatioRoot_one, map_one]

/-- Reduction turns the crossed Kummer quotient into a multiplicative character because inertia
acts trivially on the residue field. -/
theorem tameResidueCharFun_mul (σ τ : localInertiaGroup v) :
    tameResidueCharFun v (σ * τ) =
      tameResidueCharFun v σ * tameResidueCharFun v τ := by
  have hcalc :
      ((↑(tameKummerRatioRoot v (σ * τ)) :
          (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ) :
          IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) =
        σ.1 • (((↑(tameKummerRatioRoot v τ) :
          (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
          IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) *
        (((↑(tameKummerRatioRoot v σ) :
          (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))ˣ)) :
          IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) := by
    apply Subtype.ext
    change (σ.1 * τ.1) (tameKummerRoot v) / tameKummerRoot v =
      σ.1 (τ.1 (tameKummerRoot v) / tameKummerRoot v) *
        (σ.1 (tameKummerRoot v) / tameKummerRoot v)
    exact galoisRatio_mul v σ.1 τ.1 (tameKummerRoot_ne_zero v)
  let red := restrictRootsOfUnity
    (IsLocalRing.residue
      (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
    (Nat.card (κ 𝒪ᵥ) - 1)
  have hred : red (tameKummerRatioRoot v (σ * τ)) =
      red (tameKummerRatioRoot v σ) * red (tameKummerRatioRoot v τ) := by
    apply rootsOfUnity.coe_injective
    simp only [red, restrictRootsOfUnity_coe_apply,
      Subgroup.coe_mul, Units.val_mul]
    rw [hcalc, map_mul, localInertia_residue_smul_eq]
    exact mul_comm _ _
  change (residueUnitsEquivRootsOfUnity_at_place v).symm
      (red (tameKummerRatioRoot v (σ * τ))) =
    (residueUnitsEquivRootsOfUnity_at_place v).symm
        (red (tameKummerRatioRoot v σ)) *
      (residueUnitsEquivRootsOfUnity_at_place v).symm
        (red (tameKummerRatioRoot v τ))
  rw [← map_mul]
  exact congrArg (residueUnitsEquivRootsOfUnity_at_place v).symm hred

/-- The tame Kummer character on local inertia, valued in the base residue-field units. -/
noncomputable def tameResidueChar : localInertiaGroup v →* (κ 𝒪ᵥ)ˣ where
  toFun := tameResidueCharFun v
  map_one' := tameResidueCharFun_one v
  map_mul' := tameResidueCharFun_mul v

/-- An arbitrary choice of an (arithmetic) frobenious element of a local galois group. -/
noncomputable
def Field.AbsoluteGaloisGroup.adicArithFrob : Γ Kᵥ :=
  arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

lemma Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob :
    IsArithFrobAt 𝒪ᵥ Frobᵥ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :=
  .arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
