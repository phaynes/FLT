/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.JointImageAlgebra

/-! Kernel-axiom audit for the Brauer--Nesbitt joint-image structural tranche. -/

@[expose] public section

open FLT.Components.BrauerNesbitt

#print axioms jointImageAlgHom_surjective
#print axioms isSemisimpleModule_fst
#print axioms isSemisimpleModule_snd
#print axioms faithfulSMul_prod
#print axioms representationEquivOfJointImageLinearEquiv
#print axioms nonempty_representationEquiv_of_jointImageLinearEquiv
#print axioms isSemisimpleRing_jointImageAlgebra

end
