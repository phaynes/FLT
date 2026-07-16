/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLT.Assumptions.Mazur
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Instances.ZMod

/-!
Kernel-clean source boundary for the Mazur--Serre Frey irreducibility route.

This file does not assert the deep source theorems. It freezes the missing semistability,
finite-torsion, and reducible-character interfaces using concrete repository types, and proves
the terminal numerical contradiction once the geometric route supplies `4p` rational torsion
points.
-/

namespace FLTMethodology.Mazur

open scoped WeierstrassCurve.Affine

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- A global Weierstrass curve over `Q` is semistable when, at every rational prime,
its chosen minimal local model has either good or multiplicative reduction. -/
def IsSemistableOverQ (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (l : ℕ) (hl : l.Prime),
    letI : Fact l.Prime := ⟨hl⟩
    let E_l := (E.baseChange ℚ_[l]).minimal ℤ_[l]
    E_l.HasGoodReduction ℤ_[l] ∨ E_l.HasMultiplicativeReduction ℤ_[l]

/-- The finite, non-vacuous numerical consequence needed from Mazur's torsion theorem.
The finiteness field prevents `Set.ncard` from silently returning zero on an infinite set. -/
def RationalTorsionBound16 (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite ∧
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16

/-- A curve has full rational two-torsion when its `2`-torsion has exactly four points. -/
def HasFullRationalTwoTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  Set.ncard (AddSubgroup.torsionBy (E⁄ℚ).Point (2 : ℤ) : Set (E⁄ℚ).Point) = 4

/-- The exact numerical output needed after the two Serre character cases and odd-isogeny
transport have been assembled. -/
def HasLargeRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : Prop :=
  4 * p ≤ (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard

/-- Once the geometry supplies `4p` rational torsion points, the remaining contradiction is
pure arithmetic. -/
theorem not_hasLargeRationalTorsion_of_bound16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ)
    (hp : 5 ≤ p) (hbound : RationalTorsionBound16 E) :
    ¬ HasLargeRationalTorsion E p := by
  intro hlarge
  dsimp only [HasLargeRationalTorsion] at hlarge
  have hupper := hbound.2
  omega

variable (p : ℕ) [Fact p.Prime]

/-- The mod-`p` cyclotomic character obtained from the existing `p`-adic character. -/
noncomputable def modPCyclotomic (g : Γ ℚ) : ZMod p :=
  ZMod.ringEquivCongr (by simp)
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv).val.toZModPow 1)

universe uV

/-- Exact linear-algebraic content of Serre's semistable reducible-character dichotomy.

The stable line and quotient are both exposed, their sequence is exact, and their characters are
trivial and mod-`p` cyclotomic in one of the two possible orders. This structure freezes the source
output; it does not claim that every reducible semistable elliptic-curve representation supplies
such data.
-/
structure SemistableReducibleCharacterDichotomy
    (V : Type uV) [AddCommGroup V] [Module (ZMod p) V]
    (rho : GaloisRep ℚ (ZMod p) V) where
  line : ZMod p →ₗ[ZMod p] V
  line_injective : Function.Injective line
  quotient : V →ₗ[ZMod p] ZMod p
  quotient_surjective : Function.Surjective quotient
  exact : LinearMap.ker quotient = LinearMap.range line
  characters :
    ((∀ g : Γ ℚ, ∀ x : ZMod p, rho g (line x) = line x) ∧
      (∀ g : Γ ℚ, ∀ v : V,
        quotient (rho g v) = modPCyclotomic p g * quotient v)) ∨
    ((∀ g : Γ ℚ, ∀ x : ZMod p,
        rho g (line x) = line (modPCyclotomic p g * x)) ∧
      (∀ g : Γ ℚ, ∀ v : V, quotient (rho g v) = quotient v))

#check IsSemistableOverQ
#check RationalTorsionBound16
#check HasFullRationalTwoTorsion
#check HasLargeRationalTorsion
#check not_hasLargeRationalTorsion_of_bound16
#check modPCyclotomic
#check SemistableReducibleCharacterDichotomy

#print axioms IsSemistableOverQ
#print axioms RationalTorsionBound16
#print axioms HasFullRationalTwoTorsion
#print axioms HasLargeRationalTorsion
#print axioms not_hasLargeRationalTorsion_of_bound16
#print axioms modPCyclotomic
#print axioms SemistableReducibleCharacterDichotomy

end FLTMethodology.Mazur
