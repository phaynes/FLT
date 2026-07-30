/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Class-field object interfaces

This file defines the bounded idele objects used by the first class-field slice. Character and
globalisation interfaces remain methodology-only until a later source-approved slice selects them.
-/

@[expose] public section

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

noncomputable def principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range

abbrev IdeleClassGroup := (AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K

/-- Embed the multiplicative monoid of finite adeles into the full adele monoid by putting `1` at
every infinite place. This is intentionally a monoid homomorphism, not a ring homomorphism. -/
noncomputable def finiteAdeleToAdele :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K :=
  MonoidHom.inr (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

/-- The induced map from finite ideles to full ideles. -/
noncomputable def finiteIdeleEmbedding :
    (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleToAdele K)

/-- A chosen full idele which is a uniformiser at `v`, one at every other finite place, and one at
every infinite place. -/
noncomputable def localUniformiserIdele
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 K))] :
    (AdeleRing (𝓞 K) K)ˣ :=
  finiteIdeleEmbedding K (IsDedekindDomain.FiniteAdeleRing.localUniformiserUnit K v)

instance instIsMulCommutativeIdeleClassGroup :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b =>
    QuotientGroup.induction_on a fun x =>
      QuotientGroup.induction_on b fun y => by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]⟩⟩

end FLT.PotentialModularity.ClassField
