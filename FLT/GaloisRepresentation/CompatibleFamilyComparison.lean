/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.RankTwo
public import FLT.Deformations.RepresentationTheory.GaloisRepFamily

/-!
# Rank-two comparison from dense Galois data

This file isolates the deterministic topological and representation-theoretic part of the
Chebotarev comparison used by the FLT programme.  It deliberately accepts density as an explicit
hypothesis: establishing that the relevant Frobenius conjugacy classes are dense is the separate
number-theoretic Chebotarev boundary.
-/

@[expose] public section

namespace FLT.CompatibleFamily

open FLT.Components.BrauerNesbitt

universe uK uk uV uW

variable {K : Type uK} {k : Type uk} {V : Type uV} {W : Type uW}
variable [Field K]
variable [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
variable [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The union of the conjugacy classes of a family of group elements.  Chebotarev supplies
density for a set of this form, rather than for one arbitrarily chosen representative per prime. -/
def conjugacySaturation {G ι : Type*} [Group G] (elements : ι → G) : Set G :=
  {g | ∃ i x, g = x * elements i * x⁻¹}

omit [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] in
/-- Characteristic polynomials of a representation are constant on conjugacy classes. -/
theorem charpoly_conjugate {G : Type*} [Group G]
    (rho : Representation k G V) (x g : G) :
    (rho (x * g * x⁻¹)).charpoly = (rho g).charpoly := by
  have hxLeft : Function.LeftInverse (rho x⁻¹) (rho x) := by
    intro v
    simp
  have hxRight : Function.RightInverse (rho x⁻¹) (rho x) := by
    intro v
    simp
  let e : V ≃ₗ[k] V :=
    { toLinearMap := rho x
      invFun := rho x⁻¹
      left_inv := hxLeft
      right_inv := hxRight }
  have he : rho (x * g * x⁻¹) = e.conj (rho g) := by
    ext v
    rw [map_mul, map_mul]
    rfl
  rw [he, LinearEquiv.charpoly_conj]

/-- Equality of characteristic polynomials on a dense subset of the absolute Galois group extends
to every element for continuous rank-two representations.  This is the deterministic adapter
needed after a Chebotarev density theorem; it does not itself establish density. -/
theorem charpoly_eq_of_dense_of_finrank_eq_two
    (rho : GaloisRep K k V) (sigma : GaloisRep K k W)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    {S : Set (Γ K)} (hS : Dense S)
    (hchar : Set.EqOn (fun g => (rho g).charpoly) (fun g => (sigma g).charpoly) S) :
    ∀ g, (rho g).charpoly = (sigma g).charpoly := by
  letI := moduleTopology k (Module.End k V)
  letI := moduleTopology k (Module.End k W)
  have htraceV : Continuous (fun g => LinearMap.trace k V (rho g)) :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.trace k V)).comp rho.continuous
  have htraceW : Continuous (fun g => LinearMap.trace k W (sigma g)) :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.trace k W)).comp sigma.continuous
  have htraceOn : Set.EqOn
      (fun g => LinearMap.trace k V (rho g))
      (fun g => LinearMap.trace k W (sigma g)) S := by
    intro g hg
    exact trace_eq_of_charpoly_eq (rho g) (sigma g) (hchar hg)
  have htrace : (fun g => LinearMap.trace k V (rho g)) =
      (fun g => LinearMap.trace k W (sigma g)) :=
    Continuous.ext_on hS htraceV htraceW htraceOn
  have hdetV : Continuous (fun g => LinearMap.det (rho g)) :=
    IsModuleTopology.continuous_det.comp rho.continuous
  have hdetW : Continuous (fun g => LinearMap.det (sigma g)) :=
    IsModuleTopology.continuous_det.comp sigma.continuous
  have hdetOn : Set.EqOn
      (fun g => LinearMap.det (rho g)) (fun g => LinearMap.det (sigma g)) S := by
    intro g hg
    have hp := hchar hg
    change (rho g).charpoly = (sigma g).charpoly at hp
    rw [LinearMap.charpoly_of_finrank_eq_two hV,
      LinearMap.charpoly_of_finrank_eq_two hW] at hp
    have hc := congrArg (fun p : Polynomial k => p.coeff 0) hp
    change LinearMap.det (rho g) = LinearMap.det (sigma g)
    simpa using hc
  have hdet : (fun g => LinearMap.det (rho g)) =
      (fun g => LinearMap.det (sigma g)) :=
    Continuous.ext_on hS hdetV hdetW hdetOn
  intro g
  rw [LinearMap.charpoly_of_finrank_eq_two hV,
    LinearMap.charpoly_of_finrank_eq_two hW, congrFun htrace g, congrFun hdet g]

/-- Continuous semisimple rank-two Galois representations are equivalent when their
characteristic polynomials agree on a dense subset.  The theorem consumes, rather than hides, the
density premise that a separate Chebotarev theorem must provide. -/
theorem nonempty_equiv_of_dense_charpoly_eq
    (rho : GaloisRep K k V) (sigma : GaloisRep K k W)
    (hrho : Representation.IsSemisimpleRepresentation rho.toRepresentation)
    (hsigma : Representation.IsSemisimpleRepresentation sigma.toRepresentation)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    {S : Set (Γ K)} (hS : Dense S)
    (hchar : Set.EqOn (fun g => (rho g).charpoly) (fun g => (sigma g).charpoly) S) :
    Nonempty (Representation.Equiv rho.toRepresentation sigma.toRepresentation) := by
  apply nonempty_representationEquiv_of_finrank_eq_two
    rho.toRepresentation sigma.toRepresentation hrho hsigma hV hW
  exact charpoly_eq_of_dense_of_finrank_eq_two rho sigma hV hW hS hchar

/-- A Chebotarev-shaped form of the rank-two comparison: equality only has to be supplied for one
representative from each indexed conjugacy class, while density is asserted for the whole union of
those classes. -/
theorem nonempty_equiv_of_dense_conjugacy_charpoly_eq
    {ι : Type*} (elements : ι → Γ K)
    (rho : GaloisRep K k V) (sigma : GaloisRep K k W)
    (hrho : Representation.IsSemisimpleRepresentation rho.toRepresentation)
    (hsigma : Representation.IsSemisimpleRepresentation sigma.toRepresentation)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (hDense : Dense (conjugacySaturation elements))
    (hchar : ∀ i, (rho (elements i)).charpoly = (sigma (elements i)).charpoly) :
    Nonempty (Representation.Equiv rho.toRepresentation sigma.toRepresentation) := by
  apply nonempty_equiv_of_dense_charpoly_eq rho sigma hrho hsigma hV hW hDense
  rintro g ⟨i, x, rfl⟩
  change (rho (x * elements i * x⁻¹)).charpoly =
    (sigma (x * elements i * x⁻¹)).charpoly
  have hrhoConj := charpoly_conjugate rho.toRepresentation x (elements i)
  have hsigmaConj := charpoly_conjugate sigma.toRepresentation x (elements i)
  change (rho (x * elements i * x⁻¹)).charpoly = (rho (elements i)).charpoly at hrhoConj
  change (sigma (x * elements i * x⁻¹)).charpoly =
    (sigma (elements i)).charpoly at hsigmaConj
  exact hrhoConj.trans ((hchar i).trans hsigmaConj.symm)

section NumberField

open IsDedekindDomain NumberField

variable [NumberField K]

local notation "Ω" K => HeightOneSpectrum (𝓞 K)
local notation "Frob" v => Field.AbsoluteGaloisGroup.adicArithFrob v

/-- A chosen global image of the local arithmetic Frobenius at `v`.  Its conjugacy class is the
canonical datum; the chosen algebraic-closure embedding only selects a representative. -/
noncomputable def globalArithFrob (v : Ω K) : Γ K :=
  Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) (Frob v)

omit [IsTopologicalRing k] [T2Space k] in
/-- Evaluating a global representation at the chosen global Frobenius is definitionally the same
as evaluating its localization at the repository's chosen local arithmetic Frobenius. -/
theorem charpoly_globalArithFrob (rho : GaloisRep K k V) (v : Ω K) :
    (rho (globalArithFrob v)).charpoly = (rho.toLocal v (Frob v)).charpoly := rfl

/-- Global Frobenius representatives outside the finite exceptional set `S`. -/
noncomputable def frobeniusOutside (S : Finset (Ω K)) : {v : Ω K // v ∉ S} → Γ K :=
  fun v => globalArithFrob v

/-- Frobenius-conjugacy density outside one finite exceptional set.  This is a proposition, not an
axiom: the deterministic comparison below takes a proof of it explicitly. -/
def FrobeniusConjugacyDensityAt (S : Finset (Ω K)) : Prop :=
  Dense (conjugacySaturation (frobeniusOutside S))

/-- The exact arithmetic-density contract required by the live FLT base field.  It is deliberately
specialized to `ℚ`, quantified over every finite exceptional set, and contains no representation-
theoretic conclusion.  No witness is asserted in this file. -/
def RatArithmeticFrobeniusConjugacyDensity : Prop :=
  ∀ S : Finset (Ω ℚ), FrobeniusConjugacyDensityAt S

/-- Rank-two Galois representations with equal characteristic polynomials at every Frobenius
outside a finite exceptional set are equivalent, conditional only on the exact Chebotarev density
contract for that set.  The local-to-global Frobenius identification is definitional. -/
theorem nonempty_representationEquiv_of_charFrob_eq_of_density
    (rho : GaloisRep K k V) (sigma : GaloisRep K k W)
    (hrho : Representation.IsSemisimpleRepresentation rho.toRepresentation)
    (hsigma : Representation.IsSemisimpleRepresentation sigma.toRepresentation)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (S : Finset (Ω K)) (hDensity : FrobeniusConjugacyDensityAt S)
    (hchar : ∀ v : Ω K, v ∉ S →
      (rho.toLocal v (Frob v)).charpoly = (sigma.toLocal v (Frob v)).charpoly) :
    Nonempty (Representation.Equiv rho.toRepresentation sigma.toRepresentation) := by
  apply nonempty_equiv_of_dense_conjugacy_charpoly_eq
    (frobeniusOutside S) rho sigma hrho hsigma hV hW hDensity
  intro v
  exact hchar v v.property

/-- Compatibility restated using the public `GaloisRep.charFrob` name.  This adds no mathematical
content; it prevents downstream consumers from depending on the definition's local expression. -/
theorem GaloisRepFamily.isCompatible_charFrob_eq
    {E : Type*} [Field E] [NumberField E] {d : ℕ}
    {family : GaloisRepFamily K E d} (hcompat : family.isCompatible) :
    ∃ (S : Finset (Ω K)) (Pv : (Ω K) → Polynomial E),
      ∀ {p : ℕ} (hfp : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p])
        (v : Ω K),
        v ∉ S → (p : 𝓞 K) ∉ v.asIdeal →
          (family hfp φ).IsUnramifiedAt v ∧
            (family hfp φ).charFrob v = (Pv v).map φ := by
  rcases hcompat with ⟨S, Pv, hcompat⟩
  refine ⟨S, Pv, ?_⟩
  intro p hfp φ v hvS hvp
  simpa [GaloisRep.charFrob] using hcompat hfp φ v hvS hvp

end NumberField

end FLT.CompatibleFamily

end
