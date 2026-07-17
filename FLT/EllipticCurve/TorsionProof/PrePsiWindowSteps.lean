module

public import FLT.EllipticCurve.TorsionProof.EllipticTorsionSourceBoundary
public import FLT.EllipticCurve.TorsionProof.PrePsiWindowAlgebra

/-!
# Binary induction for the normalized EDS window

The generic ideal-membership certificates live in `PrePsiWindowAlgebra`. This module attaches them
to Mathlib's concrete `prePsi` binary recurrences, discharges both parity cases, and exports the
unconditional all-natural synchronized Kummer ladder.
-/

@[expose] public section

namespace FLTMethodology.Torsion

open Polynomial

variable {k : Type*} [Field k]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Rewriting six concrete recurrences onto the expanded product and sum certificates needs budget.
theorem prePsiWindow_evenCenter_transport
    (E : WeierstrassCurve k) (r : ℤ) (hr : Even r)
    (hm : PrePsiWindowRelation E (r - 1))
    (h0 : PrePsiWindowRelation E r)
    (hp : PrePsiWindowRelation E (r + 1)) :
    PrePsiWindowRelation E (2 * r) ∧ PrePsiWindowRelation E (2 * r + 1) := by
  have hrm1 : ¬Even (r - 1) := by
    intro h
    exact (Int.even_sub_one.mp h) hr
  have hrp1 : ¬Even (r + 1) := by
    intro h
    exact (Int.even_add_one.mp h) hr
  simp only [PrePsiWindowRelation, hrm1, if_false] at hm
  simp only [PrePsiWindowRelation, hr, if_pos] at h0
  simp only [PrePsiWindowRelation, hrp1, if_false] at hp
  have hmProd :
      E.preΨ (r + 1) * E.preΨ (r - 3) =
        E.Ψ₂Sq ^ 2 * (E.preΨ r * E.preΨ (r - 2)) - E.Ψ₃ * E.preΨ (r - 1) ^ 2 := by
    simpa only [show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring,
      show r - 1 - 1 = r - 2 by ring] using hm.1
  have hmSum :
      E.preΨ (r - 2) ^ 2 * E.preΨ (r + 1) +
          E.preΨ (r - 3) * E.preΨ r ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ (r - 2) * E.preΨ (r - 1) * E.preΨ r -
          E.preΨ (r - 1) ^ 3 := by
    simpa only [show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring] using hm.2
  have h0Prod :
      E.preΨ (r + 2) * E.preΨ (r - 2) =
        E.preΨ (r + 1) * E.preΨ (r - 1) - E.Ψ₃ * E.preΨ r ^ 2 := by
    exact h0.1
  have h0Sum :
      E.preΨ (r - 1) ^ 2 * E.preΨ (r + 2) +
          E.preΨ (r - 2) * E.preΨ (r + 1) ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ (r - 1) * E.preΨ r * E.preΨ (r + 1) -
          E.Ψ₂Sq ^ 2 * E.preΨ r ^ 3 := by
    exact h0.2
  have hpProd :
      E.preΨ (r + 3) * E.preΨ (r - 1) =
        E.Ψ₂Sq ^ 2 * (E.preΨ (r + 2) * E.preΨ r) -
          E.Ψ₃ * E.preΨ (r + 1) ^ 2 := by
    simpa only [show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r + 1 - 1 = r by ring] using hp.1
  have hpSum :
      E.preΨ r ^ 2 * E.preΨ (r + 3) +
          E.preΨ (r - 1) * E.preΨ (r + 2) ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ r * E.preΨ (r + 1) * E.preΨ (r + 2) -
          E.preΨ (r + 1) ^ 3 := by
    simpa only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring] using hp.2
  have hproducts := prePsiWindow_evenCenter_products
    (E.Ψ₂Sq ^ 2) E.Ψ₃ (6 * X ^ 2 + C E.b₂ * X + C E.b₄)
    (E.preΨ (r - 3)) (E.preΨ (r - 2)) (E.preΨ (r - 1)) (E.preΨ r)
    (E.preΨ (r + 1)) (E.preΨ (r + 2)) (E.preΨ (r + 3))
    hmProd hmSum h0Prod h0Sum hpProd hpSum
  have hsums := prePsiWindow_evenCenter_sums
    (E.Ψ₂Sq ^ 2) E.Ψ₃ (6 * X ^ 2 + C E.b₂ * X + C E.b₄)
    (E.preΨ (r - 3)) (E.preΨ (r - 2)) (E.preΨ (r - 1)) (E.preΨ r)
    (E.preΨ (r + 1)) (E.preΨ (r + 2)) (E.preΨ (r + 3))
    hmProd hmSum h0Prod h0Sum hpProd hpSum
  dsimp only at hproducts hsums
  constructor
  · simp only [PrePsiWindowRelation, if_pos (even_two_mul r)]
    rw [show 2 * r + 2 = 2 * (r + 1) by ring, E.preΨ_even (r + 1),
      show 2 * r - 2 = 2 * (r - 1) by ring, E.preΨ_even (r - 1),
      E.preΨ_odd r, show 2 * r - 1 = 2 * (r - 1) + 1 by ring,
      E.preΨ_odd (r - 1), E.preΨ_even r]
    simp only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring,
      hr, hrm1, if_pos, if_false, mul_one]
    constructor
    · exact hproducts.1
    · exact hsums.1
  · simp only [PrePsiWindowRelation, if_neg (Int.not_even_two_mul_add_one r)]
    rw [show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by ring, E.preΨ_odd (r + 1),
      show 2 * r + 1 - 2 = 2 * (r - 1) + 1 by ring, E.preΨ_odd (r - 1),
      show 2 * r + 1 + 1 = 2 * (r + 1) by ring, E.preΨ_even (r + 1),
      show 2 * r + 1 - 1 = 2 * r by ring, E.preΨ_even r, E.preΨ_odd r]
    simp only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 + 1 = r by ring,
      hr, hrm1, hrp1, if_pos, if_false, mul_one]
    constructor
    · exact hproducts.2
    · exact hsums.2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The parity-dual transport expands the same six concrete recurrence windows.
theorem prePsiWindow_oddCenter_transport
    (E : WeierstrassCurve k) (r : ℤ) (hr : ¬Even r)
    (hm : PrePsiWindowRelation E (r - 1))
    (h0 : PrePsiWindowRelation E r)
    (hp : PrePsiWindowRelation E (r + 1)) :
    PrePsiWindowRelation E (2 * r) ∧ PrePsiWindowRelation E (2 * r + 1) := by
  have hrm1 : Even (r - 1) := Int.even_sub_one.mpr hr
  have hrp1 : Even (r + 1) := Int.even_add_one.mpr hr
  simp only [PrePsiWindowRelation, hrm1, if_pos] at hm
  simp only [PrePsiWindowRelation, hr, if_false] at h0
  simp only [PrePsiWindowRelation, hrp1, if_pos] at hp
  have hmProd :
      E.preΨ (r + 1) * E.preΨ (r - 3) =
        E.preΨ r * E.preΨ (r - 2) - E.Ψ₃ * E.preΨ (r - 1) ^ 2 := by
    simpa only [show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring,
      show r - 1 - 1 = r - 2 by ring] using hm.1
  have hmSum :
      E.preΨ (r - 2) ^ 2 * E.preΨ (r + 1) +
          E.preΨ (r - 3) * E.preΨ r ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ (r - 2) * E.preΨ (r - 1) * E.preΨ r -
          E.Ψ₂Sq ^ 2 * E.preΨ (r - 1) ^ 3 := by
    simpa only [show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring] using hm.2
  have h0Prod :
      E.preΨ (r + 2) * E.preΨ (r - 2) =
        E.Ψ₂Sq ^ 2 * (E.preΨ (r + 1) * E.preΨ (r - 1)) -
          E.Ψ₃ * E.preΨ r ^ 2 := by
    exact h0.1
  have h0Sum :
      E.preΨ (r - 1) ^ 2 * E.preΨ (r + 2) +
          E.preΨ (r - 2) * E.preΨ (r + 1) ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ (r - 1) * E.preΨ r * E.preΨ (r + 1) -
          E.preΨ r ^ 3 := by
    exact h0.2
  have hpProd :
      E.preΨ (r + 3) * E.preΨ (r - 1) =
        E.preΨ (r + 2) * E.preΨ r - E.Ψ₃ * E.preΨ (r + 1) ^ 2 := by
    simpa only [show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r + 1 - 1 = r by ring] using hp.1
  have hpSum :
      E.preΨ r ^ 2 * E.preΨ (r + 3) +
          E.preΨ (r - 1) * E.preΨ (r + 2) ^ 2 =
        (6 * X ^ 2 + C E.b₂ * X + C E.b₄) *
            E.preΨ r * E.preΨ (r + 1) * E.preΨ (r + 2) -
          E.Ψ₂Sq ^ 2 * E.preΨ (r + 1) ^ 3 := by
    simpa only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring] using hp.2
  have hproducts := prePsiWindow_oddCenter_products
    (E.Ψ₂Sq ^ 2) E.Ψ₃ (6 * X ^ 2 + C E.b₂ * X + C E.b₄)
    (E.preΨ (r - 3)) (E.preΨ (r - 2)) (E.preΨ (r - 1)) (E.preΨ r)
    (E.preΨ (r + 1)) (E.preΨ (r + 2)) (E.preΨ (r + 3))
    hmProd hmSum h0Prod h0Sum hpProd hpSum
  have hsums := prePsiWindow_oddCenter_sums
    (E.Ψ₂Sq ^ 2) E.Ψ₃ (6 * X ^ 2 + C E.b₂ * X + C E.b₄)
    (E.preΨ (r - 3)) (E.preΨ (r - 2)) (E.preΨ (r - 1)) (E.preΨ r)
    (E.preΨ (r + 1)) (E.preΨ (r + 2)) (E.preΨ (r + 3))
    hmProd hmSum h0Prod h0Sum hpProd hpSum
  dsimp only at hproducts hsums
  constructor
  · simp only [PrePsiWindowRelation, if_pos (even_two_mul r)]
    rw [show 2 * r + 2 = 2 * (r + 1) by ring, E.preΨ_even (r + 1),
      show 2 * r - 2 = 2 * (r - 1) by ring, E.preΨ_even (r - 1),
      E.preΨ_odd r, show 2 * r - 1 = 2 * (r - 1) + 1 by ring,
      E.preΨ_odd (r - 1), E.preΨ_even r]
    simp only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 - 2 = r - 3 by ring,
      show r - 1 + 1 = r by ring,
      hr, hrm1, if_pos, if_false, mul_one]
    constructor
    · exact hproducts.1
    · exact hsums.1
  · simp only [PrePsiWindowRelation, if_neg (Int.not_even_two_mul_add_one r)]
    rw [show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by ring, E.preΨ_odd (r + 1),
      show 2 * r + 1 - 2 = 2 * (r - 1) + 1 by ring, E.preΨ_odd (r - 1),
      show 2 * r + 1 + 1 = 2 * (r + 1) by ring, E.preΨ_even (r + 1),
      show 2 * r + 1 - 1 = 2 * r by ring, E.preΨ_even r, E.preΨ_odd r]
    simp only [show r + 1 - 1 = r by ring,
      show r + 1 + 2 = r + 3 by ring,
      show r + 1 - 2 = r - 1 by ring,
      show r + 1 + 1 = r + 2 by ring,
      show r - 1 - 1 = r - 2 by ring,
      show r - 1 + 2 = r + 1 by ring,
      show r - 1 + 1 = r by ring,
      hr, hrm1, hrp1, if_pos, if_false, mul_one]
    constructor
    · exact hproducts.2
    · exact hsums.2

theorem prePsiWindowEvenStep (E : WeierstrassCurve k) :
    PrePsiWindowEvenStep E := by
  intro m _h1 h2 h3 h4 _h5
  let r : ℤ := m + 3
  have hm : PrePsiWindowRelation E (r - 1) := by
    simpa only [r, Nat.cast_add, Nat.cast_ofNat,
      show (m : ℤ) + 3 - 1 = (m + 2 : ℕ) by omega] using h2
  have h0 : PrePsiWindowRelation E r := by
    simpa only [r, Nat.cast_add, Nat.cast_ofNat] using h3
  have hp : PrePsiWindowRelation E (r + 1) := by
    simpa only [r, Nat.cast_add, Nat.cast_ofNat,
      show (m : ℤ) + 3 + 1 = (m + 4 : ℕ) by omega] using h4
  by_cases hr : Even r
  · simpa only [r, Nat.cast_add, Nat.cast_ofNat] using
      (prePsiWindow_evenCenter_transport E r hr hm h0 hp).1
  · simpa only [r, Nat.cast_add, Nat.cast_ofNat] using
      (prePsiWindow_oddCenter_transport E r hr hm h0 hp).1

theorem prePsiWindowOddStep (E : WeierstrassCurve k) :
    PrePsiWindowOddStep E := by
  intro m h1 h2 h3 _h4
  let r : ℤ := m + 2
  have hrm_eq : r - 1 = ((m + 1 : ℕ) : ℤ) := by
    simp only [r, Nat.cast_add]
    omega
  have hm : PrePsiWindowRelation E (r - 1) := by
    rw [hrm_eq]
    exact h1
  have h0 : PrePsiWindowRelation E r := by
    simpa only [r, Nat.cast_add, Nat.cast_ofNat] using h2
  have hp : PrePsiWindowRelation E (r + 1) := by
    rw [show r + 1 = ((m + 3 : ℕ) : ℤ) by
      simp only [r, Nat.cast_add, Nat.cast_ofNat]
      omega]
    exact h3
  by_cases hr : Even r
  · simpa only [r, Nat.cast_add, Nat.cast_ofNat] using
      (prePsiWindow_evenCenter_transport E r hr hm h0 hp).2
  · simpa only [r, Nat.cast_add, Nat.cast_ofNat] using
      (prePsiWindow_oddCenter_transport E r hr hm h0 hp).2

theorem prePsiWindowRelation_nat (E : WeierstrassCurve k) (n : ℕ) :
    PrePsiWindowRelation E n :=
  prePsiWindowRelation_nat_of_steps E
    (prePsiWindowEvenStep E) (prePsiWindowOddStep E) n

theorem kummerDivisionPolynomialLadder_nat
    (E : WeierstrassCurve k) (n : ℕ) :
    KummerDivisionPolynomialLadder E n :=
  kummerDivisionPolynomialLadder_of_prePsiWindow E n
    (prePsiWindowRelation_nat E n)

theorem kummerDivisionPolynomialRecurrence_nat
    (E : WeierstrassCurve k) (n : ℕ) :
    KummerDivisionPolynomialRecurrence E n :=
  (kummerDivisionPolynomialLadder_nat E n).1

theorem kummerDivisionPolynomialMiddleRecurrence_nat
    (E : WeierstrassCurve k) (n : ℕ) :
    KummerDivisionPolynomialMiddleRecurrence E n :=
  (kummerDivisionPolynomialLadder_nat E n).2

#print axioms prePsiWindow_evenCenter_transport
#print axioms prePsiWindow_oddCenter_transport
#print axioms prePsiWindowEvenStep
#print axioms prePsiWindowOddStep
#print axioms prePsiWindowRelation_nat
#print axioms kummerDivisionPolynomialLadder_nat
#print axioms kummerDivisionPolynomialRecurrence_nat
#print axioms kummerDivisionPolynomialMiddleRecurrence_nat

end FLTMethodology.Torsion
