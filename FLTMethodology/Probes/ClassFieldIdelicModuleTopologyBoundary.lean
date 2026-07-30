/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.PotentialModularity.ClassField.IdelicModuleTopology

/-!
# Class-field idelic-module topology boundary probe

This methodology-only file checks the four continuity declarations and the two closed-kernel
declarations while retaining the established T3 and negative compactness controls.

It does not state compactness, quotient-kernel comparison, reciprocity, globalization, consumer
closure, or parent-obligation closure.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

example : Continuous (finiteIdeleModule K) :=
  finiteIdeleModule_continuous K

example : Continuous (infiniteIdeleModule K) :=
  infiniteIdeleModule_continuous K

example : Continuous (ideleModule K) :=
  ideleModule_continuous K

example : Continuous (ideleClassModule K) :=
  ideleClassModule_continuous K

example : IsClosed (NormOneIdeles K : Set (AdeleRing (𝓞 K) K)ˣ) :=
  normOneIdeles_isClosed K

example : IsClosed (NormOneIdeleClassKernel K : Set (IdeleClassGroup K)) :=
  normOneIdeleClassKernel_isClosed K

#synth T3Space (NormOneIdeleClassGroup K)

/--
error: failed to synthesize
  CompactSpace (NormOneIdeleClassGroup K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassGroup K)

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.finiteIdeleModule_continuous
#print axioms FLT.PotentialModularity.ClassField.infiniteIdeleModule_continuous
#print axioms FLT.PotentialModularity.ClassField.ideleModule_continuous
#print axioms FLT.PotentialModularity.ClassField.ideleClassModule_continuous
#print axioms FLT.PotentialModularity.ClassField.normOneIdeles_isClosed
#print axioms FLT.PotentialModularity.ClassField.normOneIdeleClassKernel_isClosed
