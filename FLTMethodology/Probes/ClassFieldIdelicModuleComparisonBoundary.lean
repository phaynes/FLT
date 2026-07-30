/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
import FLT.PotentialModularity.ClassField.IdelicModuleComparison

/-!
# Class-field idelic-module comparison boundary probe

This methodology-only file consumes the norm-one idele quotient/kernel comparison while checking
that its retained T3 topology is intact and neither compactness instance has been introduced.

Compactness, reciprocity, globalization, parent closure, and promotion remain outside this slice.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

noncomputable example : NormOneIdeles K →ₜ* IdeleClassGroup K :=
  normOneIdelesToClass K

example :
    (normOneIdelesToClass K).ker = principalNormOneIdeles K :=
  normOneIdelesToClass_ker K

example :
    (normOneIdelesToClass K).range = NormOneIdeleClassKernel K :=
  normOneIdelesToClass_range K

example : Topology.IsStrictMap (normOneIdelesToClass K) :=
  normOneIdelesToClass_isStrictMap K

noncomputable example : NormOneIdeleClassGroup K ≃ₜ* NormOneIdeleClassKernel K :=
  normOneIdeleClassQuotientEquivKernel K

example (s : Set (NormOneIdeleClassGroup K)) :
    IsCompact (normOneIdeleClassQuotientEquivKernel K '' s) ↔ IsCompact s :=
  normOneIdeleClassQuotientEquivKernel_isCompact_image K s

#synth T3Space (NormOneIdeleClassGroup K)

/--
error: failed to synthesize
  CompactSpace (NormOneIdeleClassGroup K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassGroup K)

/--
error: failed to synthesize
  CompactSpace ↥(NormOneIdeleClassKernel K)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth CompactSpace (NormOneIdeleClassKernel K)

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.normOneIdelesToClass
#print axioms FLT.PotentialModularity.ClassField.normOneIdelesToClass_ker
#print axioms FLT.PotentialModularity.ClassField.normOneIdelesToClass_range
#print axioms FLT.PotentialModularity.ClassField.normOneIdelesToClass_isStrictMap
#print axioms FLT.PotentialModularity.ClassField.normOneIdeleClassQuotientEquivKernel
#print axioms
  FLT.PotentialModularity.ClassField.normOneIdeleClassQuotientEquivKernel_isCompact_image
