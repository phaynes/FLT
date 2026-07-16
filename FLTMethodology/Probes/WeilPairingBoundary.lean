import FLT.KnownIn1980s.EllipticCurves.WeilPairing

/-!
Kernel regression for the open `FLT-TATE-WEIL` construction boundary.

The current exported type of `WeierstrassCurve.weilPairing` is inhabited by the zero map. This
probe records that the zero inhabitant cannot satisfy the frozen Tate normalization consumer at a
nontrivial root of unity. It does not construct the Weil pairing or close an admission.
-/

open scoped WeierstrassCurve.Affine

namespace FLTMethodology.WeilPairing

variable {k : Type*} [Field k] [IsSepClosed k] [DecidableEq k]
variable (E : WeierstrassCurve k) [E.IsElliptic]
variable (n : ℕ) [NeZero (n : k)]

abbrev Torsion := AddSubgroup.torsionBy (E⁄k).Point (n : ℤ)

/-- The present pairing type alone does not exclude this mathematically wrong inhabitant. -/
def zeroPairing :
    Torsion E n →+ Torsion E n →+ Additive (rootsOfUnity n k) :=
  0

/-- At a nontrivial root of unity, the zero inhabitant cannot prove the normalization equation
required by `WeierstrassCurve.weilPairing_tatePoint`. -/
theorem zeroPairing_ne_nontrivial_value
    (P Q : Torsion E n) (ζ : rootsOfUnity n k) (hζ : ζ ≠ 1) :
    zeroPairing E n P Q ≠ Additive.ofMul ζ := by
  change Additive.ofMul (1 : rootsOfUnity n k) ≠ Additive.ofMul ζ
  intro h
  exact hζ (Additive.ofMul.injective h).symm

#check zeroPairing
#check zeroPairing_ne_nontrivial_value
#print axioms zeroPairing
#print axioms zeroPairing_ne_nontrivial_value

end FLTMethodology.WeilPairing
