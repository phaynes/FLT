/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.PotentialModularity.ClassField.Objects

/-!
# Class-field character boundary probe

This methodology-only file tests the smallest currently nameable class-field object layer. It does
not state reciprocity, character-existence, discreteness, profiniteness, or automorphy theorems.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

/-- Methodology-only predicate recording that the image of a proposed rank-one Galois character is
finite. This is not yet part of the public class-field API. -/
def IsFiniteOrderCharacter
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

/-- Methodology-only interface for matching a proposed global character with selected local
components. It records no existence or globalisation theorem. -/
def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
#print axioms FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
#print axioms FLT.PotentialModularity.ClassField.principalIdeles
#print axioms FLT.PotentialModularity.ClassField.IdeleClassGroup
