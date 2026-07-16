/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Quaternion relative-index component adapter

This module isolates the group-theoretic endpoint of the quaternionic stabilizer argument. To prove
that `H` has finite relative index in `K`, it is enough to map `K` into a finite group with kernel
`H.subgroupOf K`.

The theorem does not construct the integral quaternion order or its finite unit quotient. Those are
the mathematical provider obligations recorded by the FLT methodology programme.
-/

@[expose] public section

namespace FLT.Components.QuaternionRelativeIndex

/-- A finite quotient model of a subgroup proves finite relative index of its stated kernel.

In the quaternion application, `K` is the adelic stabilizer, `H` is the scalar subgroup, and `Q`
will be a finite image in the units of a quaternion order modulo scalar units. -/
theorem isFiniteRelIndex_of_finite_quotient_model
    {G Q : Type*} [Group G] [Group Q]
    {H K : Subgroup G}
    (phi : K →* Q) [Finite Q]
    (hker : phi.ker = H.subgroupOf K) :
    H.IsFiniteRelIndex K := by
  haveI : Finite phi.range := inferInstance
  haveI : phi.ker.FiniteIndex := Subgroup.finiteIndex_ker phi
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  rw [← hker]
  infer_instance

end FLT.Components.QuaternionRelativeIndex
