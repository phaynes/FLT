/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.PrePsiFormalGroupAdapter

/-!
# Descending `preΨ'` separability from an algebraic closure

The explicit repeated-root witness is naturally constructed over an algebraically closed field,
where every common irreducible factor has a root.  The frozen provider is stronger: its base field
is only separably closed and may be imperfect.  This module closes that interface mismatch by
base-changing the polynomial and curve to `AlgebraicClosure k`, applying the concrete formal-group
adapter there, and descending polynomial separability along the injective field map.

The remaining mathematical input is therefore a concrete adapter for the base-changed elliptic
curve.  No perfectness or accidental `IsAlgClosed k` assumption is added to the provider boundary.
-/

namespace FLTMethodology.Torsion

open WeierstrassCurve

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- An elliptic formal-group adapter over the algebraic closure suffices to prove separability of
the original division polynomial over the base field. -/
theorem prePsi_separable_of_algebraicClosure_formalGroupAdapter
    (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    (A : PrePsiFormalGroupAdapter
      (E.map (algebraMap k (AlgebraicClosure k))) n) :
    (E.preΨ' n).Separable := by
  rw [← Polynomial.separable_map (algebraMap k (AlgebraicClosure k))]
  rw [← WeierstrassCurve.map_preΨ']
  apply prePsi_separable_of_formalGroupAdapter
  · simpa using (map_ne_zero (algebraMap k (AlgebraicClosure k))).2 hn
  · exact A

#print axioms prePsi_separable_of_algebraicClosure_formalGroupAdapter

end


end FLTMethodology.Torsion
