/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.RankTwo

/-! Kernel-axiom audit for rank-two Brauer--Nesbitt over an arbitrary field. -/

@[expose] public section

open FLT.Components.BrauerNesbitt

#print axioms SemisimpleAlgebra.nonempty_linearEquiv_of_charpoly_eq
#print axioms nonempty_representationEquiv_of_finrank_eq_two
#print axioms RankTwoContract
#print axioms rankTwoContract

end
