import FLT.KnownIn1980s.EllipticCurves.GoodReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
Exact signature probe for the point-specialization package missing from the pinned elliptic-curve
reduction API. This definition is not a proof that the package exists.
-/

namespace FLTMethodology.GoodReduction

open scoped WeierstrassCurve.Affine

/-- The specialization data sufficient to finish the prime-to-residue-characteristic
Néron--Ogg--Shafarevich direction used by the W02 lane. -/
def PointSpecializationContract
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
      [DecidableEq ksep]
    (O : ValuationSubring ksep) : Prop :=
  ∃ (ι : R →+* O) (hι : IsLocalHom ι),
    (∀ r : R, (ι r : ksep) = algebraMap k ksep (algebraMap R k r)) ∧
    letI : IsLocalHom ι := hι
    ∃ red : (E⁄ksep).Point →
        ((E.reduction R).map (IsLocalRing.ResidueField.map ι)).toProjective.Point,
      Set.InjOn red (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)) ∧
      ∀ (σ : O.decompositionSubgroup k), σ ∈ O.inertiaSubgroup k →
        ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
          red (WeierstrassCurve.Affine.Point.map (W' := E) σ.1.toAlgHom P) = red P

#check PointSpecializationContract
#print axioms PointSpecializationContract

end FLTMethodology.GoodReduction
