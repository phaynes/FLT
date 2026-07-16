/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/

import FLTMethodology.Probes.MazurSourceBoundary
import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import FLT.FreyCurve.Basic

/-!
# Semistability of the Frey curve

This kernel-clean probe proves the local semistability input to the Mazur--Serre irreducibility
route. At a prime dividing `abc`, pairwise coprimality makes `c₄` a local unit. Away from that
support, the discriminant is a local unit. These alternatives are transported to the chosen
minimal model, giving good or multiplicative reduction at every rational prime.
-/

namespace FLTMethodology.Mazur

open WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

noncomputable section

variable (P : FreyPackage) (l : ℕ) [Fact l.Prime]

private abbrev El (P : FreyPackage) (l : ℕ) [Fact l.Prime] : WeierstrassCurve ℚ_[l] :=
  P.freyCurve.baseChange ℚ_[l]

private def c4Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

private def deltaInt (P : FreyPackage) : ℤ := P.freyCurveInt.Δ

private theorem c4Int_eq_alt :
    c4Int P = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  dsimp [c4Int]
  rw [pow_mul', ← P.hFLT]
  ring

private theorem not_dvd_c4Int_of_dvd_abc (hl : l.Prime)
    (habc : (l : ℤ) ∣ P.a * P.b * P.c) : ¬(l : ℤ) ∣ c4Int P := by
  intro hc4
  have hlI := Nat.prime_iff_prime_int.mp hl
  have hc4z : (c4Int P : ZMod l) = 0 :=
    ZMod.intCast_zmod_eq_zero_iff_dvd _ l |>.2 hc4
  rw [hlI.dvd_mul] at habc
  rcases habc with hab | hc
  · rw [hlI.dvd_mul] at hab
    rcases hab with ha | hb
    · have hbnot : ¬(l : ℤ) ∣ P.b := by
        intro hlb
        exact hlI.not_dvd_one (by rw [← P.hgcdab]; exact dvd_gcd ha hlb)
      have haz : (P.a : ZMod l) = 0 :=
        ZMod.intCast_zmod_eq_zero_iff_dvd _ l |>.2 ha
      have hbz : (P.b : ZMod l) ≠ 0 := by
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hbnot
      simp [c4Int, haz, P.hp0] at hc4z
      exact hbz hc4z
    · have hanot : ¬(l : ℤ) ∣ P.a := by
        intro hla
        exact hlI.not_dvd_one (by rw [← P.hgcdab]; exact dvd_gcd hla hb)
      have hbz : (P.b : ZMod l) = 0 :=
        ZMod.intCast_zmod_eq_zero_iff_dvd _ l |>.2 hb
      have haz : (P.a : ZMod l) ≠ 0 := by
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hanot
      simp [c4Int, hbz, P.hp0] at hc4z
      exact haz hc4z
  · have hanot : ¬(l : ℤ) ∣ P.a := by
      intro hla
      exact hlI.not_dvd_one (by rw [← P.hgcdac]; exact dvd_gcd hla hc)
    have hbnot : ¬(l : ℤ) ∣ P.b := by
      intro hlb
      exact hlI.not_dvd_one (by rw [← P.hgcdbc]; exact dvd_gcd hlb hc)
    have hcz : (P.c : ZMod l) = 0 :=
      ZMod.intCast_zmod_eq_zero_iff_dvd _ l |>.2 hc
    have haz : (P.a : ZMod l) ≠ 0 := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hanot
    have hbz : (P.b : ZMod l) ≠ 0 := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hbnot
    rw [c4Int_eq_alt] at hc4z
    simp [hcz, P.hp0] at hc4z
    exact hc4z.elim haz hbz

private theorem El_c4_eq_intCast :
    (El P l).c₄ = (c4Int P : ℚ_[l]) := by
  rw [show (El P l).c₄ = algebraMap ℚ ℚ_[l] P.freyCurve.c₄ from
    P.freyCurve.map_c₄ (algebraMap ℚ ℚ_[l])]
  rw [FreyCurve.c₄]
  simp [c4Int]

private theorem El_c4_valuation_eq_one
    (hnot : ¬(l : ℤ) ∣ c4Int P) :
    (valuation ℚ_[l] (maximalIdeal ℤ_[l])) (El P l).c₄ = 1 := by
  rw [El_c4_eq_intCast]
  change (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
    (algebraMap ℤ_[l] ℚ_[l] (c4Int P : ℤ_[l])) = 1
  apply (valuation_eq_one_iff_notMem (maximalIdeal ℤ_[l])).mpr
  intro hmem
  apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal
    (c4Int P : ℤ_[l])).mp hmem)
  apply PadicInt.isUnit_iff.mpr
  rw [PadicInt.norm_intCast_eq_one_iff]
  exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hnot).symm

private theorem deltaInt_mul_two_pow :
    deltaInt P * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hcast : (deltaInt P : ℚ) = P.freyCurve.Δ := by
    rw [← FreyCurve.map P]
    simp [deltaInt, WeierstrassCurve.map_Δ]
  rw [FreyCurve.Δ] at hcast
  norm_num at hcast ⊢
  exact_mod_cast (eq_div_iff (by norm_num : (2 : ℚ) ^ 8 ≠ 0)).mp hcast

omit [Fact l.Prime] in
private theorem not_dvd_deltaInt_of_not_dvd_abc (hl : l.Prime)
    (hnot : ¬(l : ℤ) ∣ P.a * P.b * P.c) : ¬(l : ℤ) ∣ deltaInt P := by
  intro hd
  have hpow : (l : ℤ) ∣ (P.a * P.b * P.c) ^ (2 * P.p) := by
    rw [← deltaInt_mul_two_pow]
    exact dvd_mul_of_dvd_left hd _
  apply hnot
  exact (Nat.prime_iff_prime_int.mp hl).dvd_of_dvd_pow hpow

private theorem El_delta_eq_intCast :
    (El P l).Δ = (deltaInt P : ℚ_[l]) := by
  rw [show (El P l).Δ = algebraMap ℚ ℚ_[l] P.freyCurve.Δ from
    P.freyCurve.map_Δ (algebraMap ℚ ℚ_[l])]
  rw [← FreyCurve.map P]
  simp [deltaInt, WeierstrassCurve.map_Δ]

private theorem El_delta_valuation_eq_one
    (hnotabc : ¬(l : ℤ) ∣ P.a * P.b * P.c) :
    (valuation ℚ_[l] (maximalIdeal ℤ_[l])) (El P l).Δ = 1 := by
  rw [El_delta_eq_intCast]
  change (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
    (algebraMap ℤ_[l] ℚ_[l] (deltaInt P : ℤ_[l])) = 1
  apply (valuation_eq_one_iff_notMem (maximalIdeal ℤ_[l])).mpr
  intro hmem
  apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal
    (deltaInt P : ℤ_[l])).mp hmem)
  apply PadicInt.isUnit_iff.mpr
  rw [PadicInt.norm_intCast_eq_one_iff]
  exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr
    (not_dvd_deltaInt_of_not_dvd_abc P l (Fact.out : l.Prime) hnotabc)).symm

private theorem El_isIntegral : WeierstrassCurve.IsIntegral ℤ_[l] (El P l) := by
  refine ⟨P.freyCurveInt.baseChange ℤ_[l], ?_⟩
  change P.freyCurve.baseChange ℚ_[l] =
    (P.freyCurveInt.baseChange ℤ_[l]).baseChange ℚ_[l]
  rw [← FreyCurve.map P]
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map]

private theorem minimal_c4_valuation_eq_one
    (hc4 : (valuation ℚ_[l] (maximalIdeal ℤ_[l])) (El P l).c₄ = 1) :
    (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
      ((El P l).minimal ℤ_[l]).c₄ = 1 := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l] (El P l) := El_isIntegral P l
  letI : WeierstrassCurve.IsMinimal ℤ_[l] (El P l) :=
    WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one ℤ_[l] (El P l) hc4
  let D := ((El P l).exists_isMinimal ℤ_[l]).choose
  have hD : D • El P l = (El P l).minimal ℤ_[l] := rfl
  have hvu := WeierstrassCurve.valuation_u_eq_one_of_isMinimal_smul ℤ_[l] D hD
  rw [← hD, WeierstrassCurve.variableChange_c₄, map_mul]
  simp [hvu, hc4]

private theorem minimal_delta_valuation_eq_one
    (hdelta : (valuation ℚ_[l] (maximalIdeal ℤ_[l])) (El P l).Δ = 1) :
    (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
      ((El P l).minimal ℤ_[l]).Δ = 1 := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l] (El P l) := El_isIntegral P l
  let D := ((El P l).exists_isMinimal ℤ_[l]).choose
  have hD : D • El P l = (El P l).minimal ℤ_[l] := rfl
  have hback : D⁻¹ • (El P l).minimal ℤ_[l] = El P l := by
    rw [← hD, inv_smul_smul]
  have hsub := WeierstrassCurve.valuation_Δ_aux_smul_le ℤ_[l] D⁻¹
    (show WeierstrassCurve.IsIntegral ℤ_[l]
      (D⁻¹ • (El P l).minimal ℤ_[l]) by rw [hback]; infer_instance)
  have hsubc :
      (↑(WeierstrassCurve.valuation_Δ_aux ℤ_[l]
        (D⁻¹ • (El P l).minimal ℤ_[l])) : WithZero (Multiplicative ℤ)) ≤
      (↑(WeierstrassCurve.valuation_Δ_aux ℤ_[l]
        ((1 : WeierstrassCurve.VariableChange ℚ_[l]) •
          (El P l).minimal ℤ_[l])) : WithZero (Multiplicative ℤ)) :=
    Subtype.coe_le_coe.mpr hsub
  rw [hback, one_smul,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] at hsubc
  have hle : (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
      ((El P l).minimal ℤ_[l]).Δ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_Δ_eq ℤ_[l] ((El P l).minimal ℤ_[l])]
    exact valuation_le_one _ _
  apply le_antisymm hle
  simpa [hdelta] using hsubc

private theorem minimal_good_or_multiplicative :
    let M := (El P l).minimal ℤ_[l]
    M.HasGoodReduction ℤ_[l] ∨ M.HasMultiplicativeReduction ℤ_[l] := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l] (El P l) := El_isIntegral P l
  by_cases habc : (l : ℤ) ∣ P.a * P.b * P.c
  · have hc4 := El_c4_valuation_eq_one P l
      (not_dvd_c4Int_of_dvd_abc P l (Fact.out : l.Prime) habc)
    have hc4min := minimal_c4_valuation_eq_one P l hc4
    by_cases hdelta : (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
        ((El P l).minimal ℤ_[l]).Δ = 1
    · exact Or.inl { goodReduction := hdelta }
    · right
      refine { multiplicativeReduction := hc4min, badReduction := ?_ }
      have hle : (valuation ℚ_[l] (maximalIdeal ℤ_[l]))
          ((El P l).minimal ℤ_[l]).Δ ≤ 1 := by
        rw [← WeierstrassCurve.integralModel_Δ_eq ℤ_[l] ((El P l).minimal ℤ_[l])]
        exact valuation_le_one _ _
      exact lt_of_le_of_ne hle hdelta
  · have hdelta := El_delta_valuation_eq_one P l habc
    exact Or.inl { goodReduction := minimal_delta_valuation_eq_one P l hdelta }

/-- The Frey curve has good or multiplicative reduction at every rational prime. -/
theorem freyCurve_isSemistableOverQ : IsSemistableOverQ P.freyCurve := by
  intro l hl
  letI : Fact l.Prime := ⟨hl⟩
  exact minimal_good_or_multiplicative P l

#check freyCurve_isSemistableOverQ
#print axioms freyCurve_isSemistableOverQ

end
end FLTMethodology.Mazur
