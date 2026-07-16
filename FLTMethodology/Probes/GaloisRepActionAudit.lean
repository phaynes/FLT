/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.EllipticCurve.Torsion

/-!
This methodology-only audit distinguishes the kernel-clean construction of the torsion action
from its remaining dependence on the admitted elliptic-curve torsion-finiteness theorem.
-/

#print axioms WeierstrassCurve.torsionGaloisMap
#print axioms WeierstrassCurve.torsionGaloisActionHom
#print axioms WeierstrassCurve.torsionGaloisPointStabilizer_isOpen
#print axioms WeierstrassCurve.torsionGaloisActionHom_ker_isOpen
#print axioms WeierstrassCurve.galoisRep
