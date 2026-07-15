/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

import FLT.GaloisRepresentation.Automorphic

/-!
# Kernel audit for automorphic Galois-representation infrastructure

The named wrapper makes the axiom closure of the scalar-extension quaternion instance directly
auditable without adding another declaration to the verified FLT module.
-/

open scoped TensorProduct

theorem FLTMethodology.quaternionAlgebra_baseChange_audit
    {F E D : Type*}
    [Field F]
    [Field E] [Algebra F E]
    [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] :
    IsQuaternionAlgebra E (E ⊗[F] D) := inferInstance

#print axioms FLTMethodology.quaternionAlgebra_baseChange_audit
