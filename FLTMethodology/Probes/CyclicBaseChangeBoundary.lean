import FLT.GaloisRepresentation.Automorphic
import FLTMethodology.Probes.SelectedGoodRepositoryBoundary

/-!
# Cyclic-base-change bounded boundary

This methodology-only module banks four structural lemmas, a regression theorem, and eight exact
interface definitions from the reviewed cyclic-base-change repair. None of these declarations proves
the admitted public cyclic-base-change theorem or its open analytic providers.
-/

open scoped TensorProduct
open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra WeightTwoAutomorphicForm

theorem even_finrank_of_even_base
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : Even (Module.finrank ℚ F)) : Even (Module.finrank ℚ E) := by
  rw [← Module.finrank_mul_finrank ℚ F E]
  exact hF.mul_right _

theorem mem_preimageComapFinset_iff
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    w ∈ HeightOneSpectrum.preimageComapFinset
      (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) S ↔
      w.under (NumberField.RingOfIntegers F) ∈ S := by
  simp [HeightOneSpectrum.preimageComapFinset, Set.Finite.mem_toFinset]

theorem natCast_notMem_of_mem_preimageComapFinset
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hS : ∀ v ∈ S, (p : NumberField.RingOfIntegers F) ∉ v.asIdeal)
    (w : HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hw : w ∈ HeightOneSpectrum.preimageComapFinset
      (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) S) :
    (p : NumberField.RingOfIntegers E) ∉ w.asIdeal := by
  intro hpw
  refine hS (w.under (NumberField.RingOfIntegers F))
    ((mem_preimageComapFinset_iff S w).1 hw) ?_
  have : algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E)
      (p : NumberField.RingOfIntegers F) ∈ w.asIdeal := by
    rw [map_natCast]
    exact hpw
  exact Ideal.mem_comap.mpr this

theorem heckeAlgebra_algHom_ext
    {F : Type*} [Field F] [NumberField F]
    {D : Type*} [DivisionRing D] [Algebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    {R : Type*} [CommRing R]
    {p : ℕ} (data : U₁Data F R p) (hQ : data.Q = ∅)
    {A : Type*} [CommRing A] [Algebra R A]
    (π π' : HeckeAlgebra D data →ₐ[R] A)
    (h : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
      (hvS : v ∉ data.S) (hvQ : v ∉ data.Q),
      π (HeckeAlgebra.T D data v hvS hvQ) = π' (HeckeAlgebra.T D data v hvS hvQ)) :
    π = π' := by
  ext x
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨v, hvS, hvQ, rfl⟩ | ⟨v, hv, α, hα, rfl⟩
      · exact h v hvS hvQ
      · rw [hQ] at hv
        exact absurd hv (Finset.notMem_empty v)
  | algebraMap r => exact (π.commutes r).trans (π'.commutes r).symm
  | add x y hx hy ihx ihy =>
      show π (⟨x, hx⟩ + ⟨y, hy⟩) = π' (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      show π (⟨x, hx⟩ * ⟨y, hy⟩) = π' (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

open FLTMethodology.SelectedGoodBoundary

universe u

namespace FLTMethodology.CBaseRepair

/-- Pointwise scalar-twist relation between two Galois representations. -/
def IsTwistBy {K : Type*} [Field K] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ' ρ : GaloisRep K A M) (χ : GaloisRep K A A) : Prop :=
  ∀ g m, ρ' g m = χ g 1 • ρ g m

/-- The character is trivial after restriction from F to E. -/
def FactorsThroughGal (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] (χ : GaloisRep F A M) : Prop :=
  ∀ g : Field.absoluteGaloisGroup E,
    χ (Field.absoluteGaloisGroup.map (algebraMap F E) g) = 1

/-- Conditional Clifford/Schur fiber interface. This is vocabulary, not a proved theorem. -/
def BaseChangeFiberUpToTwistOfIrreducible
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
    {k : Type*} [Field k] [TopologicalSpace k] [IsAlgClosed k]
    {M : Type*} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (ρ σ : GaloisRep F k M) : Prop :=
  GaloisRep.IsIrreducible (ρ.map (algebraMap F E)) →
  (∃ e : M ≃ₗ[k] M, (ρ.map (algebraMap F E)).conj e = σ.map (algebraMap F E)) →
  ∃ (e : M ≃ₗ[k] M) (χ : GaloisRep F k k),
    FactorsThroughGal F E χ ∧ IsTwistBy (σ.conj e) ρ χ

/-- Frobenius-characteristic-polynomial transport vocabulary. -/
def FrobeniusCharpolyTransport
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [NumberField E] [Algebra F E]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    (ρ : GaloisRep F A V) (w : HeightOneSpectrum (NumberField.RingOfIntegers E)) : Prop :=
  ((ρ.map (algebraMap F E)).toLocal w
    (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly =
    ((ρ.toLocal (w.under (NumberField.RingOfIntegers F))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          (w.under (NumberField.RingOfIntegers F)))) ^
      (w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F))).charpoly

/-- The tensor-base-changed quaternion algebra has no nonunit nonzero element. -/
def BaseChangeUnitsProvider
    (F : Type u) [Field F] [NumberField F] [IsTotallyReal F]
    (E : Type u) [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E]
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D] : Prop :=
  ∀ a : E ⊗[F] D, a ≠ 0 → IsUnit a

/-- Existence of rigidification after tensor base change. -/
def BaseChangeRigidificationProvider
    (F : Type u) [Field F] [NumberField F]
    (E : Type u) [Field E] [NumberField E] [Algebra F E]
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D] : Prop :=
  Nonempty (IsQuaternionAlgebra.NumberField.WithRigidification E (E ⊗[F] D))

/-- Forward solvable base-change boundary. This definition exposes an open analytic provider. -/
def ForwardSolvableBaseChange
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    {E : Type u} [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra F E] [IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]
    (p : ℕ) [Fact p.Prime]
    (hp : 2 < Module.finrank F (CyclotomicField p F))
    (hpE : 2 < Module.finrank E (CyclotomicField p E))
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[p]) V]
      [Module.Finite (AlgebraicClosure ℚ_[p]) V] [Module.Free (AlgebraicClosure ℚ_[p]) V]
    (hV : Module.finrank (AlgebraicClosure ℚ_[p]) V = 2)
    (ρ : GaloisRep F (AlgebraicClosure ℚ_[p]) V)
    (hρirred : GaloisRep.IsIrreducible (ρ.map (algebraMap F E)))
    (hρdet : ∀ g, ρ.det g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
      (cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv))
    (hρflat : HasFlatDescentAboveEll p ρ)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    (hρunram : ∀ v ∉ S, ↑p ∉ v.asIdeal → ρ.IsUnramifiedAt v)
    (hρtame : HasGenericTameRankOneQuotient p ρ S) : Prop :=
  ρ.IsAutomorphicOfLevel p hp hV S →
    (ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset
        (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) S)

/-- Solvable base-change descent boundary. This definition exposes open analytic providers. -/
def SolvableBaseChangeDescent
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    {E : Type u} [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra F E] [IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]
    (p : ℕ) [Fact p.Prime]
    (hp : 2 < Module.finrank F (CyclotomicField p F))
    (hpE : 2 < Module.finrank E (CyclotomicField p E))
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[p]) V]
      [Module.Finite (AlgebraicClosure ℚ_[p]) V] [Module.Free (AlgebraicClosure ℚ_[p]) V]
    (hV : Module.finrank (AlgebraicClosure ℚ_[p]) V = 2)
    (ρ : GaloisRep F (AlgebraicClosure ℚ_[p]) V)
    (hρirred : GaloisRep.IsIrreducible (ρ.map (algebraMap F E)))
    (hρdet : ∀ g, ρ.det g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
      (cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv))
    (hρflat : HasFlatDescentAboveEll p ρ)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    (hρunram : ∀ v ∉ S, ↑p ∉ v.asIdeal → ρ.IsUnramifiedAt v)
    (hρtame : HasGenericTameRankOneQuotient p ρ S) : Prop :=
  (ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset
        (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) S) →
    ρ.IsAutomorphicOfLevel p hp hV S

/-- A trivial two-dimensional representation is reducible. This regression guards the conditional
fiber interface against the quadratic one-plus-epsilon counterexample to the deleted statement. -/
theorem not_isIrreducible_trivial_two_dim
    {k G : Type*} [Field k] [Monoid G] :
    ¬ Representation.IsIrreducible (Representation.trivial k (G := G) (V := k × k)) := by
  intro h
  let N : Subrepresentation (Representation.trivial k (G := G) (V := k × k)) :=
    ⟨LinearMap.ker (LinearMap.snd k k k), by intro g v hv; simpa using hv⟩
  rcases h.eq_bot_or_eq_top N with hb | ht
  · have h10 : ((1 : k), (0 : k)) ∈ N.toSubmodule := by
      simp [N, LinearMap.mem_ker]
    rw [congrArg Subrepresentation.toSubmodule hb] at h10
    have h10' : ((1 : k), (0 : k)) ∈ (⊥ : Submodule k (k × k)) := h10
    simpa using h10'
  · have h01 : ((0 : k), (1 : k)) ∉ N.toSubmodule := by
      simp [N, LinearMap.mem_ker]
    rw [congrArg Subrepresentation.toSubmodule ht] at h01
    exact h01 Submodule.mem_top

end FLTMethodology.CBaseRepair

#print axioms even_finrank_of_even_base
#print axioms mem_preimageComapFinset_iff
#print axioms natCast_notMem_of_mem_preimageComapFinset
#print axioms heckeAlgebra_algHom_ext
#print axioms FLTMethodology.CBaseRepair.IsTwistBy
#print axioms FLTMethodology.CBaseRepair.FactorsThroughGal
#print axioms FLTMethodology.CBaseRepair.BaseChangeFiberUpToTwistOfIrreducible
#print axioms FLTMethodology.CBaseRepair.FrobeniusCharpolyTransport
#print axioms FLTMethodology.CBaseRepair.BaseChangeUnitsProvider
#print axioms FLTMethodology.CBaseRepair.BaseChangeRigidificationProvider
#print axioms FLTMethodology.CBaseRepair.ForwardSolvableBaseChange
#print axioms FLTMethodology.CBaseRepair.SolvableBaseChangeDescent
#print axioms FLTMethodology.CBaseRepair.not_isIrreducible_trivial_two_dim
