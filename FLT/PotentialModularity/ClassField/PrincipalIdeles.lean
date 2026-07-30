/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.PotentialModularity.ClassField.Objects
public import FLT.NumberField.AdeleRing
public import FLT.Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Principal ideles

This file proves the discrete and closed embeddings needed for the bounded idele-class quotient.
-/

@[expose] public section

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

instance instDiscreteTopologyPrincipalIdeles :
    DiscreteTopology (principalIdeles K) := by
  obtain ⟨U, hUopen, hU1⟩ := NumberField.AdeleRing.discrete K 1
  rw [discreteTopology_iff_isOpen_singleton_one]
  have hset : ({1} : Set (principalIdeles K)) =
      (fun u : principalIdeles K =>
        ((u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ⁻¹' U := by
    ext u
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      have h1 : (1 : K) ∈ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U := by
        rw [hU1]; exact Set.mem_singleton _
      simpa using h1
    · intro hUmem
      obtain ⟨x, hx⟩ := u.2
      have hval : ((u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
          = algebraMap K (AdeleRing (𝓞 K) K) (x : K) := by
        rw [← hx, Units.coe_map]; rfl
      rw [hval] at hUmem
      have hx1 : (x : K) = 1 := by
        have hmem : (x : K) ∈ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U :=
          Set.mem_preimage.mpr hUmem
        rw [hU1] at hmem; exact hmem
      have hxone : x = 1 := Units.ext hx1
      apply Subtype.ext
      simp only [OneMemClass.coe_one]
      rw [← hx, hxone, map_one]
  rw [hset]
  exact hUopen.preimage (Units.continuous_val.comp continuous_subtype_val)

theorem principalIdeles_isClosed :
    IsClosed ((principalIdeles K) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  Subgroup.isClosed_of_discrete

end FLT.PotentialModularity.ClassField
