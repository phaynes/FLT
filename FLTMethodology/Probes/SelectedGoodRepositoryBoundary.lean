import FLT.GaloisRepresentation.Automorphic
import FLT.ModularityLifting.Conditions

/-!
The `FLT-SGOOD-SELECTED` repository-side boundary: the five frozen, standard-trio-clean vocabulary
units selected to match Taylor 2018. Each unit is structurally a verbatim hypothesis slot of
`cyclic_base_change` but references no sorried declaration, so each audits to
`[propext, Classical.choice, Quot.sound]`.

Three boundaries are kept deliberately separate: the generic-fibre tame rank-one quotient, the
integral-model flat descent, and `BlueprintSGood.traceOnJ`. The `traceOnJ ↔ tame-quotient` bridge and
the `HasIntegralModel ↔ HasFlatDescentAboveEll` implication remain named open obligations, not silent
identifications. This file contains only these five definitions — no crystalline/Hodge–Tate/RACAR
vocabulary, no bridge proof, and no consumer-exactness example.
-/

namespace FLTMethodology.SelectedGoodBoundary

open IsDedekindDomain NumberField FLT.ModularityLifting
open scoped NumberField TensorProduct

/-- Repository-side boundary: the proved blueprint bundle plus support of `S` away from `ell`.
Carries NO automorphy conclusion, NO crystalline/HT condition, NO tame quotient. -/
structure SelectedGoodRepository
    {F : Type*} [Field F] [NumberField F]
    (ell : ℕ) [Fact ell.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[ell] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (rho : GaloisRep F R V)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop
    extends BlueprintSGood ell rho S where
  supportAwayEll : ∀ w ∈ S, ↑ell ∉ w.asIdeal

/-- Generic-fibre tame rank-one quotient — verbatim `cyclic_base_change.hρtame`, over
`AlgebraicClosure ℚ_[ell]`, `V : Type` (universe 0, as the consumer fixes it). -/
def HasGenericTameRankOneQuotient
    {F : Type*} [Field F] [NumberField F] (ell : ℕ) [Fact ell.Prime]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
    (rho : GaloisRep F (AlgebraicClosure ℚ_[ell]) V)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ w ∈ S, ∃ (π : V →ₗ[AlgebraicClosure ℚ_[ell]] AlgebraicClosure ℚ_[ell])
    (_ : Function.Surjective π)
    (δ : GaloisRep (w.adicCompletion F) (AlgebraicClosure ℚ_[ell]) (AlgebraicClosure ℚ_[ell])),
    localTameAbelianInertiaGroup w ≤ δ.ker ∧
    ∀ (g : Field.absoluteGaloisGroup (w.adicCompletion F)) (v : V),
      π ((rho.toLocal w) g v) = δ g (π v)

/-- Flat descent above `ell` — verbatim `cyclic_base_change.hρflat`: an integral model over a finite
free local `ℤ_[ell]`-algebra `R ⊆ ℚ_[ell]ᵃˡᵍ`, flat at every `v | ell`. `R V₀ : Type`,
`Module.rank R V₀ = 2`, exactly as the consumer states them. -/
def HasFlatDescentAboveEll
    {F : Type*} [Field F] [NumberField F] (ell : ℕ) [Fact ell.Prime]
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[ell]) V]
      [Module.Finite (AlgebraicClosure ℚ_[ell]) V] [Module.Free (AlgebraicClosure ℚ_[ell]) V]
    (rho : GaloisRep F (AlgebraicClosure ℚ_[ell]) V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[ell] R) (_ : IsLocalRing R) (_ : IsDomain R)
    (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : Module.Finite ℤ_[ell] R) (_ : Module.Free ℤ_[ell] R) (_ : IsModuleTopology ℤ_[ell] R)
    (_ : Algebra R (AlgebraicClosure ℚ_[ell]))
    (_ : IsScalarTower ℤ_[ell] R (AlgebraicClosure ℚ_[ell]))
    (_ : ContinuousSMul R (AlgebraicClosure ℚ_[ell]))
    (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
    (_ : Module.Free R V₀) (_ : Module.rank R V₀ = 2)
    (ρ₀ : GaloisRep F R V₀)
    (r₀ : (AlgebraicClosure ℚ_[ell]) ⊗[R] V₀ ≃ₗ[AlgebraicClosure ℚ_[ell]] V),
  (ρ₀.baseChange (AlgebraicClosure ℚ_[ell])).conj r₀ = rho ∧
  ∀ v : HeightOneSpectrum (𝓞 F), ↑ell ∈ v.asIdeal → ρ₀.IsFlatAt v

/-- The cyclotomic-degree hypothesis of `IsAutomorphicOfLevel`, named once. A property of `(F, ell)`
only — deliberately NOT a field of any representation bundle. -/
def CyclotomicDegreeBound (F : Type*) [Field F] [NumberField F] (ell : ℕ) : Prop :=
  2 < Module.finrank F (CyclotomicField ell F)

/-- Taylor's fixed identification of the `ell`-adic and complex algebraic closures — data, not a
`Prop`; not constructible in the Mathlib pin; carried by `SourceHypotheses`. -/
def ComplexEmbeddingData (ell : ℕ) [Fact ell.Prime] : Type :=
  (AlgebraicClosure ℚ_[ell]) →+* ℂ

end FLTMethodology.SelectedGoodBoundary
