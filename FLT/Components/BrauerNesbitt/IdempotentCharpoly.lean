/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.JointImageAlgebra
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Projection

/-!
# Characteristic polynomials of idempotent actions

An idempotent endomorphism is conjugate to the identity on its range times the zero map on its
kernel. Its characteristic polynomial therefore records the dimension of its range. This avoids
trace-character arguments, which can lose multiplicity information over imperfect fields.
-/

@[expose] public section

open Polynomial

namespace FLT.Components.BrauerNesbitt

universe uK uA uM uN

variable {k : Type uK} [Field k]

/-- The characteristic polynomial of an idempotent endomorphism records the dimension of its
range as the multiplicity of the root `1`. -/
theorem LinearMap.charpoly_of_isIdempotentElem
    {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (f : Module.End k M) (hf : IsIdempotentElem f) :
    f.charpoly =
      X ^ (Module.finrank k M - Module.finrank k (LinearMap.range f)) *
        (X - 1) ^ Module.finrank k (LinearMap.range f) := by
  calc
    f.charpoly = (LinearMap.id.prodMap (0 : Module.End k (LinearMap.ker f))).charpoly := by
      rw [(LinearMap.IsIdempotentElem.isProj_range f hf).eq_conj_prodMap,
        LinearEquiv.charpoly_conj]
    _ = (X - 1) ^ Module.finrank k (LinearMap.range f) *
        X ^ Module.finrank k (LinearMap.ker f) := by
      rw [show LinearMap.id = (1 : Module.End k (LinearMap.range f)) by rfl,
        LinearMap.charpoly_prodMap, LinearMap.charpoly_one, LinearMap.charpoly_zero]
    _ = X ^ (Module.finrank k M - Module.finrank k (LinearMap.range f)) *
        (X - 1) ^ Module.finrank k (LinearMap.range f) := by
      rw [show Module.finrank k (LinearMap.ker f) =
          Module.finrank k M - Module.finrank k (LinearMap.range f) by
        apply Nat.eq_sub_of_add_eq
        simpa [Nat.add_comm] using LinearMap.finrank_range_add_finrank_ker f]
      ac_rfl

/-- The characteristic polynomial of the action of an idempotent algebra element records the
dimension of its image on the module. -/
theorem charpoly_lsmul_of_isIdempotentElem
    {A : Type uA} [Ring A] [Algebra k A]
    {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module A M] [IsScalarTower k A M]
    (e : A) (he : IsIdempotentElem e) :
    LinearMap.charpoly (Algebra.lsmul k k M e) =
      X ^ (Module.finrank k M - Module.finrank k
        (LinearMap.range (Algebra.lsmul k k M e))) *
      (X - 1) ^ Module.finrank k
        (LinearMap.range (Algebra.lsmul k k M e)) := by
  exact LinearMap.charpoly_of_isIdempotentElem _ (he.map (Algebra.lsmul k k M))

/-- The multiplicity of `1` in the characteristic polynomial of an idempotent endomorphism is the
dimension of its range. -/
theorem LinearMap.rootMultiplicity_one_charpoly_of_isIdempotentElem
    {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (f : Module.End k M) (hf : IsIdempotentElem f) :
    rootMultiplicity (1 : k) f.charpoly = Module.finrank k (LinearMap.range f) := by
  rw [LinearMap.charpoly_of_isIdempotentElem f hf]
  change rootMultiplicity (1 : k)
    (X ^ (Module.finrank k M - Module.finrank k (LinearMap.range f)) *
      (X - C (1 : k)) ^ Module.finrank k (LinearMap.range f)) =
        Module.finrank k (LinearMap.range f)
  rw [rootMultiplicity_mul_X_sub_C_pow
    (pow_ne_zero _ (X_ne_zero : (X : k[X]) ≠ 0))]
  simp

/-- Equal characteristic polynomials of idempotent endomorphisms force their image dimensions to
agree, even when the two endomorphisms act on different finite-dimensional spaces. -/
theorem LinearMap.finrank_range_eq_of_charpoly_eq_of_isIdempotentElem
    {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    [AddCommGroup N] [Module k N] [Module.Finite k N]
    (f : Module.End k M) (g : Module.End k N)
    (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hchar : f.charpoly = g.charpoly) :
    Module.finrank k (LinearMap.range f) = Module.finrank k (LinearMap.range g) := by
  calc
    Module.finrank k (LinearMap.range f) = rootMultiplicity (1 : k) f.charpoly :=
      (LinearMap.rootMultiplicity_one_charpoly_of_isIdempotentElem f hf).symm
    _ = rootMultiplicity (1 : k) g.charpoly := congrArg (rootMultiplicity (1 : k)) hchar
    _ = Module.finrank k (LinearMap.range g) :=
      LinearMap.rootMultiplicity_one_charpoly_of_isIdempotentElem g hg

/-- Equal characteristic polynomials of two idempotent algebra actions force equality of the
dimensions of their images. -/
theorem finrank_range_lsmul_eq_of_charpoly_eq_of_isIdempotentElem
    {A : Type uA} [Ring A] [Algebra k A]
    {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module.Finite k N]
    [Module A N] [IsScalarTower k A N]
    (e : A) (he : IsIdempotentElem e)
    (hchar : LinearMap.charpoly (Algebra.lsmul k k M e) =
      LinearMap.charpoly (Algebra.lsmul k k N e)) :
    Module.finrank k (LinearMap.range (Algebra.lsmul k k M e)) =
      Module.finrank k (LinearMap.range (Algebra.lsmul k k N e)) := by
  exact LinearMap.finrank_range_eq_of_charpoly_eq_of_isIdempotentElem _ _
    (he.map (Algebra.lsmul k k M)) (he.map (Algebra.lsmul k k N)) hchar

end FLT.Components.BrauerNesbitt

end
