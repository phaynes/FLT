/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.PotentialModularity.ClassField.IdelicModule

/-!
# Class-field idelic-module boundary probe

This methodology-only file checks the algebraic normalized idelic module, its principal-idele
product formula, and the norm-one quotient's inherited topology.

It does not state continuity, surjectivity, compactness, reciprocity, globalization, character
construction, consumer closure, or parent-obligation closure.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

#check finiteIdeleModule
#check infiniteIdeleModule
#check ideleModule
#check ideleModule_principal
#check principalIdeles_le_ideleModule_ker
#check ideleClassModule
#check NormOneIdeles
#check principalNormOneIdeles
#check NormOneIdeleClassGroup
#check NormOneIdeleClassKernel

#synth Group (NormOneIdeleClassGroup K)
#synth TopologicalSpace (NormOneIdeleClassGroup K)
#synth IsTopologicalGroup (NormOneIdeleClassGroup K)
#synth T3Space (NormOneIdeleClassGroup K)

example (x : Kˣ) :
    ideleModule K
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x) = 1 :=
  ideleModule_principal K x

/--
error: failed to synthesize
  CompactSpace (NormOneIdeleClassGroup K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassGroup K)

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.finiteIdeleUnitsEquiv
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleFactor
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleFactor_hasFiniteMulSupport
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleFactor_one
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleFactor_mul
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleModule
#print axioms FLT.PotentialModularity.ClassField.infiniteIdeleUnitsEquiv
#print axioms FLT.PotentialModularity.ClassField.infiniteIdeleModule
#print axioms FLT.PotentialModularity.ClassField.ideleModule
#print axioms FLT.PotentialModularity.ClassField.finite_part
#print axioms FLT.PotentialModularity.ClassField.infinite_coord
#print axioms FLT.PotentialModularity.ClassField.principal_product
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleModule_toReal
#print axioms FLT.PotentialModularity.ClassField.infiniteIdeleModule_toReal
#print axioms FLT.PotentialModularity.ClassField.ideleModule_principal
#print axioms FLT.PotentialModularity.ClassField.principalIdeles_le_ideleModule_ker
#print axioms FLT.PotentialModularity.ClassField.ideleClassModule
#print axioms FLT.PotentialModularity.ClassField.NormOneIdeles
#print axioms FLT.PotentialModularity.ClassField.principalNormOneIdeles
#print axioms FLT.PotentialModularity.ClassField.NormOneIdeleClassGroup
#print axioms FLT.PotentialModularity.ClassField.NormOneIdeleClassKernel
#print axioms FLT.PotentialModularity.ClassField.principalNormOneIdeles_isClosed
#print axioms FLT.PotentialModularity.ClassField.instT3SpaceNormOneIdeleClassGroup
