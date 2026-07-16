/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
# Explicit Tate point-map boundary

This file isolates the exact algebraic interface between Tate's analytic point map and the
existing `WeierstrassCurve.tateCurveEquiv` provider type. Tate's Theorem 1 supplies precisely the
three data fields below: a homomorphism, surjectivity, and kernel `q ^ ℤ`.

No analytic point map is constructed here. The theorem proves that, once those source data are
formalized, Mathlib's quotient first-isomorphism theorem closes the bundled `AddEquiv` without
additional mathematics.
-/

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace TateExplicitPointMapBoundaryProbe

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [DecidableEq k]

/-- The exact data produced by the explicit Tate point map before quotienting. -/
structure ExplicitTatePointMapData (q : kˣ)
    (_hq : valuation k (q : k) < 1) where
  phi : Additive kˣ →+ ((WeierstrassCurve.tateCurve (q : k))⁄k).Point
  surjective : Function.Surjective phi
  ker_eq : phi.ker = (Subgroup.zpowers q).toAddSubgroup

/-- Proposition-valued existence contract corresponding to Tate's Theorem 1. -/
def ExplicitTatePointMapContract (q : kˣ)
    (hq : valuation k (q : k) < 1) : Prop :=
  Nonempty (ExplicitTatePointMapData q hq)

/-- Exact kernel and surjectivity turn the explicit point map into the desired quotient
equivalence. The source quotient and the provider's additive quotient are definitionally the same
type after applying `Subgroup.toAddSubgroup`. -/
noncomputable def tateCurveEquivOfExplicitPointMap
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (data : ExplicitTatePointMapData q hq) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+
      ((WeierstrassCurve.tateCurve (q : k))⁄k).Point :=
  QuotientAddGroup.liftEquiv
    (Subgroup.zpowers q).toAddSubgroup data.surjective data.ker_eq.symm

omit [IsNonarchimedeanLocalField k] in
/-- The proposition-valued source contract is sufficient for existence of the exact provider
value. Provider code may choose a witness only after the analytic contract is proved. -/
theorem nonempty_tateCurveEquiv_of_explicitPointMapContract
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (h : ExplicitTatePointMapContract q hq) :
    Nonempty
      (Additive (kˣ ⧸ Subgroup.zpowers q) ≃+
        ((WeierstrassCurve.tateCurve (q : k))⁄k).Point) :=
  h.map (tateCurveEquivOfExplicitPointMap q hq)

#check Subgroup.toAddSubgroup
#check QuotientAddGroup.liftEquiv
#print axioms tateCurveEquivOfExplicitPointMap
#print axioms nonempty_tateCurveEquiv_of_explicitPointMapContract

end TateExplicitPointMapBoundaryProbe
