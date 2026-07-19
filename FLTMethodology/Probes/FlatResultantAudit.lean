/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.KnownIn1980s.EllipticCurves.Flat

/-!
# Kernel audit for the universal division-polynomial resultant

This methodology-only audit keeps the exact target declaration and its two adjacent
kernel-clean boundary lemmas visible to reviewers.
-/

#print axioms WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default
#print axioms WeierstrassCurve.resultant_Φ_ΨSq
#print axioms WeierstrassCurve.isCoprime_Φ_ΨSq
