/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.KnownIn1980s.EllipticCurves.Torsion
public import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
This methodology-only audit records three completed transport proofs while making their remaining
dependency on admitted upstream elliptic-curve classification and Tate-uniformisation data visible.
-/

#print axioms WeierstrassCurve.torsion_rank_two
#print axioms WeierstrassCurve.tatePoint_mem_torsionBy_of_mem_rootsOfUnity
#print axioms WeierstrassCurve.tatePoint_mem_torsionBy_of_pow_eq
