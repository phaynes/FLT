import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Class-field character boundary probe

This methodology-only file tests the smallest currently nameable class-field object layer. It does
not state reciprocity, character-existence, discreteness, profiniteness, or automorphy theorems.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

def IsFiniteOrderCharacter
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv

variable (K : Type*) [Field K] [NumberField K]

noncomputable def principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range

noncomputable def IdeleClassGroup := (AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
#print axioms FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
#print axioms FLT.PotentialModularity.ClassField.principalIdeles
#print axioms FLT.PotentialModularity.ClassField.IdeleClassGroup
