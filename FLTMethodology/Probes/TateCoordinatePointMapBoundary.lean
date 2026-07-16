/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.TateExplicitPointMapBoundary
import FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction

/-!
# Tate coordinates to point-map boundary

The frozen repository already proves the formal identity satisfied by Tate's `X(u,q)` and
`Y(u,q)` series. This probe isolates the remaining route from concrete local-field coordinates to
the explicit point-map contract.

Once concrete coordinates satisfy the Tate equation away from `q ^ ℤ`, the point function is
defined to be the point at infinity on `q ^ ℤ` and the corresponding affine point elsewhere.
This definition makes its zero fibre exactly `q ^ ℤ`. Therefore the exact-kernel proof is
mechanical: only the group law and surjectivity remain as mathematical fields after coordinate
construction.
-/

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace TateCoordinatePointMapBoundaryProbe

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [DecidableEq k]

/-- Concrete local-field `X/Y` coordinates away from the cyclic period subgroup. The existing
formal `TateCurve.X`, `TateCurve.Y`, and `TateCurve.weierstrass_equation` are candidate inputs to
the construction of these data; their evaluation bridge is not assumed here. -/
structure ExplicitTateCoordinateData (q : kˣ)
    (_hq : valuation k (q : k) < 1) where
  x : kˣ → k
  y : kˣ → k
  equation : ∀ u : kˣ, u ∉ Subgroup.zpowers q →
    (WeierstrassCurve.tateCurve (q : k)).toAffine.Equation (x u) (y u)

/-- The point function obtained from concrete coordinates: period-subgroup elements map to the
point at infinity and every other unit maps to the affine Tate point. -/
noncomputable def explicitTatePointFun
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq) :
    Additive kˣ → ((WeierstrassCurve.tateCurve (q : k))⁄k).Point := by
  letI := WeierstrassCurve.isElliptic_tateCurve q hq
  intro u
  exact if hu : u.toMul ∈ Subgroup.zpowers q then 0
    else WeierstrassCurve.Affine.Point.mk (coordinates.equation u.toMul hu)

omit [DecidableEq k] in
/-- The zero fibre is exactly the period subgroup, with no analytic injectivity theorem left to
prove after the point function is defined piecewise. -/
theorem explicitTatePointFun_eq_zero_iff
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq)
    (u : Additive kˣ) :
    explicitTatePointFun q hq coordinates u = 0 ↔
      u.toMul ∈ Subgroup.zpowers q := by
  letI := WeierstrassCurve.isElliptic_tateCurve q hq
  by_cases hu : u.toMul ∈ Subgroup.zpowers q
  · simp [explicitTatePointFun, hu]
  · simp only [explicitTatePointFun, dite_false, hu, iff_false]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The two residual mathematical laws after concrete coordinates are available. `map_add`
packages Tate's addition theorem; `surjective` is the hard onto part of uniformization. -/
structure ExplicitTatePointLawData
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq) where
  map_add : ∀ u v : Additive kˣ,
    explicitTatePointFun q hq coordinates (u + v) =
      explicitTatePointFun q hq coordinates u +
        explicitTatePointFun q hq coordinates v
  surjective : Function.Surjective (explicitTatePointFun q hq coordinates)

/-- Bundle the point function and the supplied addition theorem as an additive homomorphism. -/
noncomputable def explicitTatePointHom
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq)
    (laws : ExplicitTatePointLawData q hq coordinates) :
    Additive kˣ →+ ((WeierstrassCurve.tateCurve (q : k))⁄k).Point where
  toFun := explicitTatePointFun q hq coordinates
  map_zero' := by
    letI := WeierstrassCurve.isElliptic_tateCurve q hq
    simp [explicitTatePointFun]
  map_add' := laws.map_add

/-- Concrete coordinates, the addition theorem, and surjectivity supply the exact point-map
contract. The kernel field follows from the piecewise definition rather than an additional source
assumption. -/
noncomputable def explicitTatePointMapDataOfCoordinates
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq)
    (laws : ExplicitTatePointLawData q hq coordinates) :
    TateExplicitPointMapBoundaryProbe.ExplicitTatePointMapData q hq where
  phi := explicitTatePointHom q hq coordinates laws
  surjective := laws.surjective
  ker_eq := by
    ext u
    rw [AddMonoidHom.mem_ker]
    exact explicitTatePointFun_eq_zero_iff q hq coordinates u

/-- Direct assembly into the exact admitted `tateCurveEquiv` type. -/
noncomputable def tateCurveEquivOfCoordinates
    (q : kˣ) (hq : valuation k (q : k) < 1)
    (coordinates : ExplicitTateCoordinateData q hq)
    (laws : ExplicitTatePointLawData q hq coordinates) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+
      ((WeierstrassCurve.tateCurve (q : k))⁄k).Point :=
  TateExplicitPointMapBoundaryProbe.tateCurveEquivOfExplicitPointMap q hq
    (explicitTatePointMapDataOfCoordinates q hq coordinates laws)

#check TateCurve.X
#check TateCurve.Y
#check TateCurve.weierstrass_equation
#print axioms TateCurve.weierstrass_equation
#print axioms explicitTatePointFun_eq_zero_iff
#print axioms explicitTatePointMapDataOfCoordinates
#print axioms tateCurveEquivOfCoordinates

end TateCoordinatePointMapBoundaryProbe
