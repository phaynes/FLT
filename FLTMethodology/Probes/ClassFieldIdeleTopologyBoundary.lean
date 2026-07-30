/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLTMethodology.Probes.ClassFieldCharacterBoundary
import FLT.PotentialModularity.ClassField.Components

/-!
# Class-field idele topology boundary probe

This methodology-only file checks the exact multiplicative maps needed to place a finite local
uniformiser in the full idele group. It also checks that the transparent idele-class quotient name
inherits the expected group and topology instances.

It does not state connected-component, discreteness, profiniteness, reciprocity, globalization, or
automorphy theorems.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

#synth CommGroup (IdeleClassGroup K)
#synth TopologicalSpace (IdeleClassGroup K)
#synth IsTopologicalGroup (IdeleClassGroup K)
#synth T3Space (IdeleClassGroup K)

example :
    IsClosed ((principalIdeles K) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  principalIdeles_isClosed K

-- The component quotient deliberately has one bundled group path and a proposition-level
-- commutativity mixin. These positive probes are the consumer contract for this slice.
#synth Group (ComponentGroup K)
#synth TopologicalSpace (ComponentGroup K)
#synth IsTopologicalGroup (ComponentGroup K)
#synth T3Space (ComponentGroup K)
#synth IsMulCommutative (ComponentGroup K)

example (a b : ComponentGroup K) : a * b = b * a := mul_comm' a b

-- Pin the direct-context synthesis budget so this probe necessarily exercises Mathlib's
-- sanctioned mixin-to-bundled bridge rather than the deeper quotient instance path.
set_option maxSynthPendingDepth 1 in
open scoped IsMulCommutative in
#synth CommGroup (ComponentGroup K)

-- Pin the package budget too, so direct and Lake builds exercise the same quotient instance path.
set_option maxSynthPendingDepth 3 in
#synth CommGroup (ComponentGroup K)

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.finiteAdeleToAdele
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleEmbedding
#print axioms FLT.PotentialModularity.ClassField.localUniformiserIdele
#print axioms FLT.PotentialModularity.ClassField.instIsMulCommutativeIdeleClassGroup
#print axioms FLT.PotentialModularity.ClassField.instDiscreteTopologyPrincipalIdeles
#print axioms FLT.PotentialModularity.ClassField.principalIdeles_isClosed
#print axioms FLT.PotentialModularity.ClassField.ComponentGroup
#print axioms FLT.PotentialModularity.ClassField.identityComponent_isClosed
#print axioms FLT.PotentialModularity.ClassField.instIsMulCommutativeComponentGroup
#print axioms FLT.PotentialModularity.ClassField.instT3SpaceComponentGroup
#print axioms FLT.PotentialModularity.ClassField.ideleToClass
#print axioms FLT.PotentialModularity.ClassField.ideleClassToComponent
#print axioms FLT.PotentialModularity.ClassField.ideleToComponent
#print axioms FLT.PotentialModularity.ClassField.localUniformiserComponent
