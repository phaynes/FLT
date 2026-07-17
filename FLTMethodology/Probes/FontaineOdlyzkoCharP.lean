import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic

/-!
Coefficient-characteristic leaf for the proposed Fontaine--Odlyzko route.

This module isolates a single, self-contained fact: a finite field that carries an `ℤ_[3]`-algebra
structure necessarily has characteristic `3`. The 3-adic algebra map forces every prime other
than `3` to remain a unit downstream, and a finite field cannot have characteristic `0`, so the
residue characteristic is pinned to `3`.

This is *only* the coefficient-characteristic node. It does **not** prove reducibility of the
associated residual representation, the cut-out-field construction, any discriminant bound, or the
`mod_three` congruence that the Fontaine--Odlyzko argument would ultimately need. Consequently it
does not touch `Odlyzko_statement`, `knownin1980s`, or any proposed N1/N2 assumption, and it cannot
promote `FLT-FONTAINE-ODLYZKO`.
-/

namespace FLTProbe.FontaineOdlyzko

universe u

/-- A finite field equipped with an `ℤ_[3]`-algebra structure has characteristic `3`.

Proof sketch: a finite field has some prime characteristic `q`. If `q ≠ 3` then `3 ∤ q`, so the
integer `q` has 3-adic norm `1` and is a unit in `ℤ_[3]`; its image under `algebraMap ℤ_[3] k` is
therefore a unit in `k`. But that image is `(q : k) = 0`, and `0` is not a unit in a field. Hence
`q = 3`.

This is purely the coefficient-characteristic leaf of the proposed Fontaine--Odlyzko route; see the
module docstring for what it deliberately does not establish. -/
theorem charP_three_of_zp3_algebra
    (k : Type u) [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3 := by
  obtain ⟨q, hq⟩ := CharP.exists k
  haveI := hq
  haveI qprime : Fact q.Prime := ⟨CharP.char_is_prime k q⟩
  have h3q : (3 : ℕ) ∣ q := by
    by_contra hdvd
    have hnlt : ¬ ‖((q : ℤ) : ℤ_[3])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      intro hd
      exact hdvd (by exact_mod_cast hd)
    have hnorm : ‖((q : ℤ) : ℤ_[3])‖ = 1 :=
      le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hnlt)
    have hu : IsUnit (((q : ℤ) : ℤ_[3])) := PadicInt.isUnit_iff.mpr hnorm
    have huk : IsUnit (algebraMap ℤ_[3] k ((q : ℤ) : ℤ_[3])) := hu.map (algebraMap ℤ_[3] k)
    rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero k q] at huk
    exact not_isUnit_zero huk
  have hq3 : (3 : ℕ) = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_three qprime.out).mp h3q
  subst hq3
  exact hq

#check @charP_three_of_zp3_algebra

#print axioms charP_three_of_zp3_algebra

end FLTProbe.FontaineOdlyzko
