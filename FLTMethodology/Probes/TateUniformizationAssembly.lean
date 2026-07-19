/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLT.KnownIn1980s.EllipticCurves.TateCurve
import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Tate uniformization assembly probe

This file isolates the integration step from the two mathematical inputs in the Tate
uniformization provider. It proves that the general curve equivalence is mechanically obtained
from the explicit Tate-curve equivalence and a change of variables from the Tate curve to the
given curve. It does not prove either input.
-/

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace TateUniformizationAssemblyProbe

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

variable (E : WeierstrassCurve k) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]

/-- Assemble the uniformization of `E` from the explicit Tate-curve uniformization and a
change of Weierstrass coordinates. No analytic or local-form theorem is hidden here. -/
noncomputable def assembleTateEquiv [DecidableEq k]
    (hTate : (WeierstrassCurve.tateCurve E.q).IsElliptic)
    (curveEquiv :
      Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+
        ((WeierstrassCurve.tateCurve E.q)⁄k).Point)
    (C : WeierstrassCurve.VariableChange k)
    (hC : C • WeierstrassCurve.tateCurve E.q = E) :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point := by
  letI : (WeierstrassCurve.tateCurve E.q).IsElliptic := hTate
  exact curveEquiv.trans
    ((WeierstrassCurve.Affine.Point.equivVariableChange
      (WeierstrassCurve.tateCurve E.q) C).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hC))

/-- The two provider inputs are sufficient for existence of the general Tate uniformization. -/
theorem nonempty_tateEquiv_of_components [DecidableEq k]
    (hTate : (WeierstrassCurve.tateCurve E.q).IsElliptic)
    (hCurve : Nonempty
      (Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+
        ((WeierstrassCurve.tateCurve E.q)⁄k).Point))
    (hChange : ∃ C : WeierstrassCurve.VariableChange k,
      C • WeierstrassCurve.tateCurve E.q = E) :
    Nonempty (Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point) := by
  rcases hCurve with ⟨curveEquiv⟩
  rcases hChange with ⟨C, hC⟩
  exact ⟨assembleTateEquiv E hTate curveEquiv C hC⟩

#print axioms assembleTateEquiv
#print axioms nonempty_tateEquiv_of_components
#print axioms WeierstrassCurve.tateEquivOfComponents
#print axioms WeierstrassCurve.tateEquiv

end TateUniformizationAssemblyProbe
