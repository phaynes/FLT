import FLT.FreyCurve.Basic

namespace FLTMethodology.Mazur

/-- The Frey-package normalization gives Serre's `A ≡ -1 (mod 4)` condition after
setting `A = a^p`. -/
theorem frey_A_mod_four (P : FreyPackage) :
    ((P.a ^ P.p : ℤ) : ZMod 4) = -1 := by
  push_cast
  rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, if_neg]
  exact Nat.not_even_iff_odd.mpr P.hp_odd

/-- The Frey-package normalization gives Serre's `B ≡ 0 (mod 32)` condition after
setting `B = b^p`. -/
theorem frey_B_mod_thirtyTwo (P : FreyPackage) :
    ((P.b ^ P.p : ℤ) : ZMod 32) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 32).2
  have two_dvd_b : (2 : ℤ) ∣ P.b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  calc
    (32 : ℤ) = 2 ^ 5 := by norm_num
    _ ∣ P.b ^ 5 := pow_dvd_pow_of_dvd two_dvd_b 5
    _ ∣ P.b ^ P.p := pow_dvd_pow P.b P.hp5

end FLTMethodology.Mazur

#print axioms FLTMethodology.Mazur.frey_A_mod_four
#print axioms FLTMethodology.Mazur.frey_B_mod_thirtyTwo
