/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FLTMethodology.Probes.TateSubstitutionBridge
import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Tate-curve reduction methodology probe

This file proves the integral, minimal, multiplicative, and split-multiplicative properties
of the explicit Tate curve. It remains outside the verified FLT root.
-/

open ValuativeRel
open IsLocalRing
open scoped PowerSeries.WithPiTopology

namespace TateReductionProbe

open PowerSeries

variable {k : Type*} [Field k] [TopologicalSpace k]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]

theorem valuation_evalInt_lt_one_of_constantCoeff_zero
    (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧)
    (hF : PowerSeries.constantCoeff F = 0) :
    valuation k (TateCurve.evalInt q F) < 1 := by
  have hcoeff : ∀ m < 1, PowerSeries.coeff m F = 0 := by
    intro m hm
    have : m = 0 := Nat.lt_one_iff.mp hm
    subst m
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hF
  exact (TateCurve.valuation_evalInt_le_pow q hq hcoeff).trans_lt (by simpa using hq)

theorem tateCurve_a₄_valuation_lt_one (q : k) (hq : valuation k q < 1) :
    valuation k (WeierstrassCurve.tateCurve q).a₄ < 1 := by
  rw [show (WeierstrassCurve.tateCurve q).a₄ = WeierstrassCurve.tateA₄ q by rfl,
    WeierstrassCurve.tateA₄_eq_evalInt q hq]
  apply valuation_evalInt_lt_one_of_constantCoeff_zero q hq
  simp [TateCurve.a₄Formal, TateCurve.sInt]

theorem tateCurve_a₆_valuation_lt_one (q : k) (hq : valuation k q < 1) :
    valuation k (WeierstrassCurve.tateCurve q).a₆ < 1 := by
  rw [show (WeierstrassCurve.tateCurve q).a₆ = WeierstrassCurve.tateA₆ q by rfl,
    WeierstrassCurve.tateA₆_eq_evalInt q hq]
  apply valuation_evalInt_lt_one_of_constantCoeff_zero q hq
  simp [TateCurve.a₆Formal]

theorem tateCurve_c₄_valuation_eq_one (q : k) (hq : valuation k q < 1) :
    valuation k (WeierstrassCurve.tateCurve q).c₄ = 1 := by
  rw [WeierstrassCurve.tateCurve_c₄_eq_evalInt q hq,
    TateCurve.evalInt_c₄Formal q hq]
  have ha₄ : valuation k (TateCurve.evalInt q TateCurve.a₄Formal) < 1 :=
    valuation_evalInt_lt_one_of_constantCoeff_zero q hq _ (by
      simp [TateCurve.a₄Formal, TateCurve.sInt])
  have h48 : valuation k ((48 : ℤ) : k) ≤ 1 := valuation_intCast_le_one 48
  have hprod : valuation k (((48 : ℤ) : k) * TateCurve.evalInt q TateCurve.a₄Formal) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h48 zero_le ha₄
  exact (valuation k).map_sub_eq_of_lt_left (by simpa using hprod)

theorem tateCurve_isIntegral (q : k) (hq : valuation k q < 1) :
    WeierstrassCurve.IsIntegral 𝒪[k] (WeierstrassCurve.tateCurve q) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift
  · exact ⟨1, by simp [WeierstrassCurve.tateCurve]⟩
  · exact ⟨0, by simp [WeierstrassCurve.tateCurve]⟩
  · exact ⟨0, by simp [WeierstrassCurve.tateCurve]⟩
  · exact ⟨⟨(WeierstrassCurve.tateCurve q).a₄,
      (tateCurve_a₄_valuation_lt_one q hq).le⟩, rfl⟩
  · exact ⟨⟨(WeierstrassCurve.tateCurve q).a₆,
      (tateCurve_a₆_valuation_lt_one q hq).le⟩, rfl⟩

theorem tateCurve_isMinimal (q : k) (hq : valuation k q < 1) :
    WeierstrassCurve.IsMinimal 𝒪[k] (WeierstrassCurve.tateCurve q) := by
  letI : WeierstrassCurve.IsIntegral 𝒪[k] (WeierstrassCurve.tateCurve q) :=
    tateCurve_isIntegral q hq
  apply WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one 𝒪[k]
  let c₄O : 𝒪[k] := ⟨(WeierstrassCurve.tateCurve q).c₄,
    (tateCurve_c₄_valuation_eq_one q hq).le⟩
  change (IsDiscreteValuationRing.maximalIdeal 𝒪[k]).valuation k
    (algebraMap 𝒪[k] k c₄O) = 1
  exact ValuativeRel.adicValuation_eq_one_iff.mpr (by
    change valuation k (c₄O : k) = 1
    simpa [c₄O] using tateCurve_c₄_valuation_eq_one q hq)

theorem tateCurve_Δ_valuation_eq (q : kˣ) (hq : valuation k (q : k) < 1) :
    valuation k (WeierstrassCurve.tateCurve (q : k)).Δ = valuation k (q : k) := by
  rw [WeierstrassCurve.tateCurve_Δ_eq_evalInt (q : k) hq,
    TateDeltaAnalyticBridgeProbe.weierstrassDiscriminantFormal_eq_deltaFormal]
  exact TateCurve.valuation_evalInt_eq (q : k) q.ne_zero hq
    (by rw [← TateDeltaAnalyticBridgeProbe.weierstrassDiscriminantFormal_eq_deltaFormal]
        exact TateCurve.constantCoeff_weierstrassDiscriminantFormal)
    (by rw [← TateDeltaAnalyticBridgeProbe.weierstrassDiscriminantFormal_eq_deltaFormal]
        exact TateCurve.coeff_one_weierstrassDiscriminantFormal)

theorem tateCurve_hasMultiplicativeReduction (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    (WeierstrassCurve.tateCurve (q : k)).HasMultiplicativeReduction 𝒪[k] := by
  letI : WeierstrassCurve.IsIntegral 𝒪[k]
      (WeierstrassCurve.tateCurve (q : k)) := tateCurve_isIntegral (q : k) hq
  letI : WeierstrassCurve.IsMinimal 𝒪[k]
      (WeierstrassCurve.tateCurve (q : k)) := tateCurve_isMinimal (q : k) hq
  refine { badReduction := ?_, multiplicativeReduction := ?_ }
  · let ΔO : 𝒪[k] := ⟨(WeierstrassCurve.tateCurve (q : k)).Δ,
      (tateCurve_Δ_valuation_eq q hq).le.trans hq.le⟩
    change (IsDiscreteValuationRing.maximalIdeal 𝒪[k]).valuation k
      (algebraMap 𝒪[k] k ΔO) < 1
    apply ValuativeRel.adicValuation_lt_one_iff.mpr
    change valuation k (ΔO : k) < 1
    simpa [ΔO, tateCurve_Δ_valuation_eq q hq] using hq
  · let c₄O : 𝒪[k] := ⟨(WeierstrassCurve.tateCurve (q : k)).c₄,
      (tateCurve_c₄_valuation_eq_one (q : k) hq).le⟩
    change (IsDiscreteValuationRing.maximalIdeal 𝒪[k]).valuation k
      (algebraMap 𝒪[k] k c₄O) = 1
    apply ValuativeRel.adicValuation_eq_one_iff.mpr
    change valuation k (c₄O : k) = 1
    simpa [c₄O] using tateCurve_c₄_valuation_eq_one (q : k) hq

theorem tateCurve_hasSplitMultiplicativeReduction (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    (WeierstrassCurve.tateCurve (q : k)).HasSplitMultiplicativeReduction 𝒪[k] := by
  let W := WeierstrassCurve.tateCurve (q : k)
  letI : WeierstrassCurve.IsIntegral 𝒪[k] W := tateCurve_isIntegral (q : k) hq
  letI : WeierstrassCurve.IsMinimal 𝒪[k] W := tateCurve_isMinimal (q : k) hq
  let hmult : W.HasMultiplicativeReduction 𝒪[k] :=
    tateCurve_hasMultiplicativeReduction q hq
  letI : W.HasMultiplicativeReduction 𝒪[k] := hmult
  refine { hmult with splitMultiplicativeReduction := ?_ }
  let I := W.integralModel 𝒪[k]
  let φ : 𝒪[k] →+* ResidueField 𝒪[k] := algebraMap 𝒪[k] (ResidueField 𝒪[k])
  have ha₁I : I.a₁ = 1 := by
    apply IsFractionRing.injective 𝒪[k] k
    rw [show algebraMap 𝒪[k] k I.a₁ = W.a₁ from
      WeierstrassCurve.integralModel_a₁_eq 𝒪[k] W]
    simp [W, WeierstrassCurve.tateCurve]
  have ha₂I : I.a₂ = 0 := by
    apply IsFractionRing.injective 𝒪[k] k
    rw [show algebraMap 𝒪[k] k I.a₂ = W.a₂ from
      WeierstrassCurve.integralModel_a₂_eq 𝒪[k] W]
    simp [W, WeierstrassCurve.tateCurve]
  have ha₃I : I.a₃ = 0 := by
    apply IsFractionRing.injective 𝒪[k] k
    rw [show algebraMap 𝒪[k] k I.a₃ = W.a₃ from
      WeierstrassCurve.integralModel_a₃_eq 𝒪[k] W]
    simp [W, WeierstrassCurve.tateCurve]
  have ha₄res : φ I.a₄ = 0 := by
    rw [show φ I.a₄ = residue 𝒪[k] I.a₄ by rfl, residue_eq_zero_iff]
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply mem_nonunits_iff.mpr
    apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
    change valuation k (algebraMap 𝒪[k] k I.a₄) < 1
    rw [WeierstrassCurve.integralModel_a₄_eq 𝒪[k] W]
    exact tateCurve_a₄_valuation_lt_one (q : k) hq
  have ha₆res : φ I.a₆ = 0 := by
    rw [show φ I.a₆ = residue 𝒪[k] I.a₆ by rfl, residue_eq_zero_iff]
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply mem_nonunits_iff.mpr
    apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
    change valuation k (algebraMap 𝒪[k] k I.a₆) < 1
    rw [WeierstrassCurve.integralModel_a₆_eq 𝒪[k] W]
    exact tateCurve_a₆_valuation_lt_one (q : k) hq
  have hpoly : I.nodePoly.map φ =
      (Polynomial.X : Polynomial (ResidueField 𝒪[k])) ^ 2 + Polynomial.X := by
    rw [WeierstrassCurve.nodePoly_map]
    simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, ha₁I, ha₂I, ha₃I, ha₄res, ha₆res]
  change (I.nodePoly.map φ).Splits
  rw [hpoly, show (Polynomial.X : Polynomial (ResidueField 𝒪[k])) ^ 2 +
      Polynomial.X = Polynomial.X * (Polynomial.X + 1) by ring]
  exact Polynomial.Splits.X.mul (by simpa using
    (Polynomial.Splits.X_add_C (1 : ResidueField 𝒪[k])))

#print axioms tateCurve_isMinimal
#print axioms tateCurve_hasSplitMultiplicativeReduction

end TateReductionProbe
