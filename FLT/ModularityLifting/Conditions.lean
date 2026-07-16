/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# Temporary blueprint modularity-lifting conditions

This file formalizes only the four conditions called `S`-good in the FLT blueprint. It is a
repository-local reconciliation target. In particular, it is not the statement of Taylor's 2018
automorphy-lifting theorem and carries no automorphy conclusion.
-/

@[expose] public section

namespace FLT.ModularityLifting

open IsDedekindDomain NumberField
open scoped NumberField

/-- The four conditions called `S`-good in the FLT blueprint: cyclotomic determinant,
unramifiedness outside `S` and `ell`, trace two on the tame-kernel subgroup at every place in `S`,
and flatness at the places above `ell`. -/
structure BlueprintSGood
    {F : Type*} [Field F] [NumberField F]
    (ell : Nat) [Fact ell.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[ell] R]
    {V : Type*} [AddCommGroup V] [Module R V]
      [Module.Finite R V] [Module.Free R V]
    (rho : GaloisRep F R V)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))) : Prop where
  det : ∀ g, rho.det g =
    algebraMap ℤ_[ell] R (cyclotomicCharacter (AlgebraicClosure F) ell g.toRingEquiv)
  isUnramified : ∀ v, v ∉ S → ↑ell ∉ v.asIdeal → rho.IsUnramifiedAt v
  traceOnJ : ∀ v ∈ S, ∀ sigma ∈ localTameAbelianInertiaGroup v,
    LinearMap.trace R V (rho.toLocal v sigma) = 2
  isFlat : ∀ v, ↑ell ∈ v.asIdeal → rho.IsFlatAt v

end FLT.ModularityLifting
