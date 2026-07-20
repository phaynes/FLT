/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.IdempotentCharpoly

/-! Kernel-axiom audit for characteristic polynomials of idempotent actions. -/

@[expose] public section

open FLT.Components.BrauerNesbitt

#print axioms LinearMap.charpoly_of_isIdempotentElem
#print axioms charpoly_lsmul_of_isIdempotentElem

end
