/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

module

public import FLT.EllipticCurve.TorsionProof.TorsionParityCount

/-!
# The normalized EDS on the two-torsion discriminant locus

This module proves the closed form of `preNormEDS' 0 c d` on the locus `d² = -4c³`.  The odd
terms are signed powers of a parameter `t`; the even terms additionally contain the half-index.
The latter coefficient proves the nonvanishing required at a two-torsion coordinate whenever the
index remains nonzero in the coefficient field.
-/

@[expose] public section

namespace FLTMethodology.Torsion

noncomputable section

universe u

variable {k : Type u} [Field k]

lemma monomial_square_mul_mul (A B C t : k) (a b c : ℕ) :
    (A * t ^ a) ^ 2 * (B * t ^ b) * (C * t ^ c) =
      A ^ 2 * B * C * t ^ (2 * a + b + c) := by
  rw [mul_pow]
  calc
    A ^ 2 * (t ^ a) ^ 2 * (B * t ^ b) * (C * t ^ c) =
        A ^ 2 * B * C * ((t ^ a) ^ 2 * t ^ b * t ^ c) := by ring
    _ = A ^ 2 * B * C * t ^ (2 * a + b + c) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 2
      omega

lemma monomial_mul_cube (A B t : k) (a b : ℕ) :
    (A * t ^ a) * (B * t ^ b) ^ 3 = A * B ^ 3 * t ^ (a + 3 * b) := by
  rw [mul_pow]
  calc
    A * t ^ a * (B ^ 3 * (t ^ b) ^ 3) = A * B ^ 3 * (t ^ a * (t ^ b) ^ 3) := by ring
    _ = A * B ^ 3 * t ^ (a + 3 * b) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      ring

lemma monomial_mul_mul_square (A B C t : k) (a b c : ℕ) :
    (A * t ^ a) * (B * t ^ b) * (C * t ^ c) ^ 2 =
      A * B * C ^ 2 * t ^ (a + b + 2 * c) := by
  rw [mul_pow]
  calc
    A * t ^ a * (B * t ^ b) * (C ^ 2 * (t ^ c) ^ 2) =
        A * B * C ^ 2 * (t ^ a * t ^ b * (t ^ c) ^ 2) := by ring
    _ = A * B * C ^ 2 * t ^ (a + b + 2 * c) := by
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 2
      omega

/-- The simultaneous odd/even closed-form contract for the specialized normalized EDS. -/
def SpecialEDSFormula (t : k) (n : ℕ) : Prop :=
  (∀ r : ℕ, n = 2 * r + 1 →
    preNormEDS' 0 (-t ^ 2) (-2 * t ^ 3) n =
      (-1 : k) ^ r * t ^ (r * (r + 1))) ∧
  (∀ r : ℕ, n = 2 * (r + 1) →
    preNormEDS' 0 (-t ^ 2) (-2 * t ^ 3) n =
      (-1 : k) ^ (r + 2) * (r + 1 : ℕ) * t ^ (r * (r + 2)))

/-- Closed form for every index of the normalized EDS specialized by
`b = 0`, `c = -t²`, and `d = -2t³`. -/
theorem specialEDSFormula (t : k) (n : ℕ) : SpecialEDSFormula t n := by
  induction n using normEDSRec with
  | zero =>
      constructor <;> intro r hr <;> omega
  | one =>
      constructor
      · intro r hr
        have : r = 0 := by omega
        subst r
        simp
      · intro r hr
        omega
  | two =>
      constructor
      · intro r hr
        omega
      · intro r hr
        have : r = 0 := by omega
        subst r
        simp
  | three =>
      constructor
      · intro r hr
        have : r = 1 := by omega
        subst r
        simp
      · intro r hr
        omega
  | four =>
      constructor
      · intro r hr
        omega
      · intro r hr
        have : r = 1 := by omega
        subst r
        simp
        ring
  | even m h1 h2 h3 h4 h5 =>
      constructor
      · intro r hr
        omega
      · intro r hr
        have hr : r = m + 2 := by omega
        subst r
        rw [preNormEDS'_even]
        rcases m.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
        · have e1 := h1.1 s (by omega)
          have e2 := h2.2 s (by omega)
          have e3 := h3.1 (s + 1) (by omega)
          have e4 := h4.2 (s + 1) (by omega)
          have e5 := h5.1 (s + 2) (by omega)
          rw [e1, e2, e3, e4, e5]
          rw [monomial_square_mul_mul, monomial_mul_mul_square]
          have hpow1 :
              2 * (s * (s + 2)) + (s + 1) * (s + 1 + 1) +
                  (s + 2) * (s + 2 + 1) =
                (s + s + 2) * (s + s + 2 + 2) := by ring
          have hpow2 :
              s * (s + 1) + (s + 1) * (s + 1 + 1) +
                  2 * ((s + 1) * (s + 1 + 2)) =
                (s + s + 2) * (s + s + 2 + 2) := by ring
          rw [hpow1, hpow2]
          simp only [pow_add]
          push_cast
          have hsign2 : (-1 : k) ^ (s * 2) = 1 :=
            Even.neg_one_pow ⟨s, by omega⟩
          have hsign4 : (-1 : k) ^ (s * 4) = 1 :=
            Even.neg_one_pow ⟨s * 2, by omega⟩
          norm_num
          ring_nf
          rw [hsign2, hsign4]
        · have e1 := h1.2 s (by omega)
          have e2 := h2.1 (s + 1) (by omega)
          have e3 := h3.2 (s + 1) (by omega)
          have e4 := h4.1 (s + 2) (by omega)
          have e5 := h5.2 (s + 2) (by omega)
          rw [e1, e2, e3, e4, e5]
          rw [monomial_square_mul_mul, monomial_mul_mul_square]
          have hpow1 :
              2 * ((s + 1) * (s + 1 + 1)) + (s + 1) * (s + 1 + 2) +
                  (s + 2) * (s + 2 + 2) =
                (2 * s + 1 + 2) * (2 * s + 1 + 2 + 2) := by ring
          have hpow2 :
              s * (s + 2) + (s + 1) * (s + 1 + 2) +
                  2 * ((s + 2) * (s + 2 + 1)) =
                (2 * s + 1 + 2) * (2 * s + 1 + 2 + 2) := by ring
          rw [hpow1, hpow2]
          simp only [pow_add]
          push_cast
          norm_num
          ring_nf
          rw [Even.neg_one_pow (show Even (s * 4) from ⟨s * 2, by omega⟩)]
          ring
  | odd m h1 h2 h3 h4 =>
      constructor
      · intro r hr
        have hr : r = m + 2 := by omega
        subst r
        rw [preNormEDS'_odd]
        rcases m.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
        · have e1 := h1.1 s (by omega)
          have e2 := h2.2 s (by omega)
          have e3 := h3.1 (s + 1) (by omega)
          have e4 := h4.2 (s + 1) (by omega)
          rw [e1, e2, e3, e4]
          rw [if_pos (show Even (s + s) from ⟨s, rfl⟩)]
          rw [if_pos (show Even (s + s) from ⟨s, rfl⟩)]
          simp only [mul_zero, mul_one, zero_sub]
          rw [monomial_mul_cube]
          have hpow :
              s * (s + 1) + 3 * ((s + 1) * (s + 1 + 1)) =
                (s + s + 2) * (s + s + 2 + 1) := by ring
          rw [hpow]
          simp only [pow_add]
          norm_num
          ring_nf
          rw [Even.neg_one_pow (show Even (s * 4) from ⟨s * 2, by omega⟩)]
          rw [Even.neg_one_pow (show Even (s * 2) from ⟨s, by omega⟩)]
        · have e1 := h1.2 s (by omega)
          have e2 := h2.1 (s + 1) (by omega)
          have e3 := h3.2 (s + 1) (by omega)
          have e4 := h4.1 (s + 2) (by omega)
          rw [e1, e2, e3, e4]
          rw [if_neg (Nat.not_even_two_mul_add_one s)]
          rw [if_neg (Nat.not_even_two_mul_add_one s)]
          simp only [mul_zero, mul_one, sub_zero]
          rw [monomial_mul_cube]
          have hpow :
              (s + 2) * (s + 2 + 1) + 3 * ((s + 1) * (s + 1 + 1)) =
                (2 * s + 1 + 2) * (2 * s + 1 + 2 + 1) := by ring
          rw [hpow]
          simp only [pow_add]
          norm_num
          ring_nf
          rw [Even.neg_one_pow (show Even (s * 4) from ⟨s * 2, by omega⟩)]
          ring
      · intro r hr
        omega

/-- On the discriminant locus `d² = -4c³`, every positive even term whose index remains nonzero
in the coefficient field is nonzero. -/
theorem specialEvenPreNormEDS_ne_zero {c d : k} {m : ℕ}
    (hm : Even m) (hmk : (m : k) ≠ 0) (hc : c ≠ 0)
    (hrel : d ^ 2 = -4 * c ^ 3) : preNormEDS' 0 c d m ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := by
    intro h2
    rcases hm with ⟨r, rfl⟩
    apply hmk
    rw [Nat.cast_add]
    calc
      (r : k) + (r : k) = (2 : k) * (r : k) := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hd : d ≠ 0 := by
    intro hd
    have h4 : (4 : k) ≠ 0 := by
      rw [show (4 : k) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    have : (-4 : k) * c ^ 3 = 0 := by
      rw [← hrel, hd, zero_pow (by norm_num)]
    exact (mul_ne_zero (neg_ne_zero.mpr h4) (pow_ne_zero 3 hc)) this
  let t : k := d / (2 * c)
  have ht : t ≠ 0 := div_ne_zero hd (mul_ne_zero h2 hc)
  have htc : -t ^ 2 = c := by
    dsimp only [t]
    field_simp [h2, hc]
    rw [hrel]
    ring
  have htd : -2 * t ^ 3 = d := by
    dsimp only [t]
    field_simp [h2, hc]
    rw [hrel]
    ring
  rcases hm with ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    intro hrzero
    apply hmk
    rw [hr, hrzero, Nat.cast_add, Nat.cast_zero, zero_add]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr0
  have hformula := (specialEDSFormula t m).2 q
  have hmshape : m = 2 * (q + 1) := by omega
  specialize hformula hmshape
  rw [htc, htd] at hformula
  rw [hformula]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by
    have hqcast : (q + 1 : k) ≠ 0 := by
      intro hzero
      apply hmk
      rw [hmshape, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, hzero,
        mul_zero]
    exact_mod_cast hqcast)) (pow_ne_zero _ ht)

end

end FLTMethodology.Torsion
