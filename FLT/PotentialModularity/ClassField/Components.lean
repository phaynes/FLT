/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.PotentialModularity.ClassField.PrincipalIdeles
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Idele-class components

This file defines the identity-component quotient and its canonical continuous maps.

The second quotient retains the inherited `Group` together with the proposition-level
`IsMulCommutative` mixin. At the pinned Lean/Mathlib revision, bundled
`CommGroup (ComponentGroup K)` synthesis is order-sensitive: a fresh lookup fails, explicit
construction through `QuotientGroup.Quotient.commGroup` exceeds a bounded reduction budget, yet a
later lookup can succeed after the component-group instance path has been elaborated. The
transparent `IdeleClassGroup` quotient exposes competing inherited group and commutative-group
reduction paths. This is an elaboration-stability boundary, not a mathematical non-existence claim.
The supported deterministic contract for this slice is the inherited `Group`,
`IsMulCommutative`, and `mul_comm'`.
-/

@[expose] public section

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- The quotient of the idele class group by its identity component. -/
abbrev ComponentGroup :=
  IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)

theorem identityComponent_isClosed :
    IsClosed ((Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) :=
  isClosed_connectedComponent

/-- Commutativity for the component quotient, exposed as a proposition-level mixin so that the
inherited quotient `Group` remains the unique bundled group structure. -/
instance instIsMulCommutativeComponentGroup :
    IsMulCommutative (ComponentGroup K) :=
  ⟨⟨fun a b =>
    QuotientGroup.induction_on a fun x =>
      QuotientGroup.induction_on b fun y => by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm']⟩⟩

instance instT3SpaceComponentGroup : T3Space (ComponentGroup K) := by
  haveI := identityComponent_isClosed K
  infer_instance

/-- Quotient map from ideles to the idele class group, as a continuous hom. -/
noncomputable def ideleToClass :
    (AdeleRing (𝓞 K) K)ˣ →ₜ* IdeleClassGroup K where
  __ := QuotientGroup.mk' (principalIdeles K)
  continuous_toFun := QuotientGroup.continuous_mk

/-- Quotient map from the idele class group to its component group. -/
noncomputable def ideleClassToComponent :
    IdeleClassGroup K →ₜ* ComponentGroup K where
  __ := QuotientGroup.mk' (Subgroup.connectedComponentOfOne (IdeleClassGroup K))
  continuous_toFun := QuotientGroup.continuous_mk

/-- Composite continuous hom from ideles to the component group. -/
noncomputable def ideleToComponent :
    (AdeleRing (𝓞 K) K)ˣ →ₜ* ComponentGroup K :=
  (ideleClassToComponent K).comp (ideleToClass K)

/-- The image of the chosen local uniformiser idele in the component group. -/
noncomputable def localUniformiserComponent
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ComponentGroup K := by
  classical
  exact ideleToComponent K (localUniformiserIdele K v)

end FLT.PotentialModularity.ClassField
