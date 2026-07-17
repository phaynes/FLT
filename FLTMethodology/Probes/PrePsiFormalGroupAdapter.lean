/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.FormalGroupLinearization
import FLTMethodology.Probes.PrePsiInfinitesimal

/-!
# The exact elliptic formal-group adapter for `preΨ'` separability

The generic formal-group calculation proves that multiplication by `n` has linear coefficient
`(n : k)`. This file states the remaining elliptic adapter without hiding it behind a separability
assumption. The adapter must send every explicit repeated-root witness to a nonzero tangent
coordinate and prove that the formal `n`-series annihilates that coordinate.

Once such an adapter is constructed, the contradiction, separability of `preΨ'`, and therefore the
already-assembled torsion count are immediate. This is an internal component interface, not a new
provider assumption.
-/

namespace FLTMethodology.Torsion

open WeierstrassCurve

noncomputable section

universe u

variable {k : Type u} [Field k]

/-- The smallest formal-group interface still required by the repeated-root witness. -/
structure PrePsiFormalGroupAdapter
    (E : WeierstrassCurve k) (n : ℕ) where
  /-- A formal group for the elliptic curve in a local coordinate at the identity. -/
  formalGroup : FormalGroup k
  /-- Translation to the identity followed by the chosen local coordinate, at first order. -/
  tangentCoordinate :
    {x : k} → PrePsiInfinitesimalWitness E n x → k
  /-- A nonconstant dual point remains nonconstant in the local coordinate. -/
  tangentCoordinate_ne_zero :
    ∀ {x : k} (w : PrePsiInfinitesimalWitness E n x), tangentCoordinate w ≠ 0
  /-- A division-polynomial infinitesimal zero lies in the infinitesimal kernel of `[n]`. -/
  nSeries_annihilates :
    ∀ {x : k} (w : PrePsiInfinitesimalWitness E n x),
      PowerSeries.coeff 1 (FLTMethodology.formalGroupNSeries formalGroup n) *
        tangentCoordinate w = 0

/-- A prime-to-characteristic multiplication map has no nonconstant infinitesimal kernel witness. -/
theorem isEmpty_prePsiInfinitesimalWitness_of_formalGroupAdapter
    (E : WeierstrassCurve k) {n : ℕ} (hn : (n : k) ≠ 0)
    (A : PrePsiFormalGroupAdapter E n) (x : k) :
    IsEmpty (PrePsiInfinitesimalWitness E n x) := by
  constructor
  intro w
  have hkill := A.nSeries_annihilates w
  rw [FLTMethodology.formalGroupNSeries_coeff_one] at hkill
  exact (mul_ne_zero hn (A.tangentCoordinate_ne_zero w)) hkill

/-- The complete separability terminal, conditional only on the concrete elliptic adapter above. -/
theorem prePsi_separable_of_formalGroupAdapter
    [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) (A : PrePsiFormalGroupAdapter E n) :
    (E.preΨ' n).Separable :=
  prePsi_separable_of_no_infinitesimalWitness E hn
    (isEmpty_prePsiInfinitesimalWitness_of_formalGroupAdapter E hn A)

end

end FLTMethodology.Torsion
