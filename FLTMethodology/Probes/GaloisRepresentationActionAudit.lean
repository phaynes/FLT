/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.EllipticCurve.Torsion

/-!
# Galois-action audit

Kernel audit for the source-independent `DistribMulAction` closure in the first bounded proof
tranche. This does not close `FLT-TATE-TORSION`; other enumerated admissions remain in that node.
-/

#print axioms WeierstrassCurve.galoisRepresentation
