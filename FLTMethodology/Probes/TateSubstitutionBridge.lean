/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FLTMethodology.Probes.TateDeltaAnalyticBridge

/-!
# Tate substitution/evaluation methodology probe

This file closes the formal-substitution/convergent-evaluation boundary needed by the
Tate-parameter construction. It remains outside the verified FLT root: the declarations
here are kernel-backed methodology evidence and are not imported by the upstream proof.
-/

open ValuativeRel
open scoped PowerSeries.WithPiTopology

namespace TateSubstitutionBridgeProbe

open PowerSeries

variable {k : Type*} [Field k] [TopologicalSpace k]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Evaluation of an integral formal substitution agrees with iterated convergent
evaluation on the open unit disc. The zero constant coefficient ensures that evaluating
the inner series stays in the open unit disc. -/
theorem evalInt_subst (q : k) (hq : valuation k q < 1)
    (G F : ℤ⟦X⟧) (hG0 : PowerSeries.constantCoeff G = 0) :
    TateCurve.evalInt q (PowerSeries.subst G F) =
      TateCurve.evalInt (TateCurve.evalInt q G) F := by
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : IsUniformAddGroup 𝒪[k] := inferInstanceAs (IsUniformAddGroup 𝒪[k].toAddSubgroup)
  have hind : Topology.IsInducing ((↑) : 𝒪[k] → k) := ⟨rfl⟩
  let qO : 𝒪[k] := ⟨q, hq.le⟩
  have hqO : PowerSeries.HasEval qO :=
    hind.tendsto_nhds_iff.mpr
      (by simpa [Function.comp_def] using TateCurve.tendsto_pow_nhds_zero hq)
  have hGcoeff : ∀ m < 1, PowerSeries.coeff m G = 0 := by
    intro m hm
    have hm0 : m = 0 := Nat.lt_one_iff.mp hm
    subst m
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hG0
  have hGval_le : valuation k (TateCurve.evalInt q G) ≤ valuation k q := by
    simpa using TateCurve.valuation_evalInt_le_pow q hq hGcoeff
  have hg : valuation k (TateCurve.evalInt q G) < 1 := hGval_le.trans_lt hq
  let gO : 𝒪[k] := ⟨TateCurve.evalInt q G, hg.le⟩
  have hgO : PowerSeries.HasEval gO :=
    hind.tendsto_nhds_iff.mpr
      (by simpa [Function.comp_def] using TateCurve.tendsto_pow_nhds_zero hg)
  have keyq : ∀ H : ℤ⟦X⟧,
      TateCurve.evalInt q H = ((PowerSeries.aeval hqO H : 𝒪[k]) : k) := by
    intro H
    change (∑' n : ℕ, ((PowerSeries.coeff n H : ℤ) : k) * q ^ n) = _
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def, qO] using (PowerSeries.hasSum_aeval hqO H).map
      (Subring.subtype 𝒪[k]).toAddMonoidHom continuous_subtype_val
  have keyg : ∀ H : ℤ⟦X⟧,
      TateCurve.evalInt (TateCurve.evalInt q G) H =
        ((PowerSeries.aeval hgO H : 𝒪[k]) : k) := by
    intro H
    change (∑' n : ℕ,
      ((PowerSeries.coeff n H : ℤ) : k) * (TateCurve.evalInt q G) ^ n) = _
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def, gO] using (PowerSeries.hasSum_aeval hgO H).map
      (Subring.subtype 𝒪[k]).toAddMonoidHom continuous_subtype_val
  have hpoint : PowerSeries.aeval hqO G = gO := by
    apply Subtype.ext
    exact (keyq G).symm
  subst gO
  have hsub : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  have hcomp := PowerSeries.comp_aeval hsub.hasEval
    (PowerSeries.continuous_aeval hqO)
  have happ :
      PowerSeries.aeval hqO (PowerSeries.aeval hsub.hasEval F) =
        PowerSeries.aeval
          (hsub.hasEval.map (PowerSeries.continuous_aeval hqO)) F := by
    simpa only [AlgHom.comp_apply] using DFunLike.congr_fun hcomp F
  have hright :
      PowerSeries.aeval
          (hsub.hasEval.map (PowerSeries.continuous_aeval hqO)) F =
        PowerSeries.aeval hgO F := by
    rw [show PowerSeries.aeval
          (hsub.hasEval.map (PowerSeries.continuous_aeval hqO)) F =
        PowerSeries.eval₂ (algebraMap ℤ 𝒪[k]) (PowerSeries.aeval hqO G) F by
          exact congrFun (PowerSeries.coe_aeval _) F]
    rw [show PowerSeries.aeval hgO F =
        PowerSeries.eval₂ (algebraMap ℤ 𝒪[k])
          (⟨TateCurve.evalInt q G, hg.le⟩ : 𝒪[k]) F by
          exact congrFun (PowerSeries.coe_aeval _) F]
    exact congrArg (fun x : 𝒪[k] ↦
      PowerSeries.eval₂ (algebraMap ℤ 𝒪[k]) x F) hpoint
  have hsubst : PowerSeries.aeval hsub.hasEval F = PowerSeries.subst G F := by
    rw [← PowerSeries.substAlgHom_eq_aeval hsub]
    exact congrFun (PowerSeries.coe_substAlgHom hsub) F
  calc
    TateCurve.evalInt q (PowerSeries.subst G F) =
        ((PowerSeries.aeval hqO (PowerSeries.subst G F) : 𝒪[k]) : k) := keyq _
    _ = ((PowerSeries.aeval hgO F : 𝒪[k]) : k) := by
      rw [← hsubst]
      exact congrArg ((↑) : 𝒪[k] → k) (happ.trans hright)
    _ = TateCurve.evalInt (TateCurve.evalInt q G) F := (keyg F).symm

/-- The formal inverse identity survives evaluation in every nonarchimedean local field. -/
theorem evalInt_jInv_jInvReverse (q : k) (hq : valuation k q < 1) :
    TateCurve.evalInt (TateCurve.evalInt q TateCurve.jInv)
        TateCurve.jInvReverse = q := by
  rw [← evalInt_subst q hq TateCurve.jInv TateCurve.jInvReverse
    TateCurve.constantCoeff_jInv]
  rw [TateCurve.subst_jInvReverse, TateCurve.evalInt_X]

/-- The other formal inverse identity also survives evaluation. -/
theorem evalInt_jInvReverse_jInv (w : k) (hw : valuation k w < 1) :
    TateCurve.evalInt (TateCurve.evalInt w TateCurve.jInvReverse)
        TateCurve.jInv = w := by
  rw [← evalInt_subst w hw TateCurve.jInvReverse TateCurve.jInv
    TateCurve.constantCoeff_jInvReverse]
  rw [TateCurve.jInv_subst_jInvReverse, TateCurve.evalInt_X]

/-- The two formal reciprocal-j series coincide after the discriminant bridge. -/
theorem weierstrassJInvFormal_eq_jInv :
    TateCurve.weierstrassJInvFormal = TateCurve.jInv := by
  rw [TateCurve.weierstrassJInvFormal, TateCurve.jInv,
    TateDeltaAnalyticBridgeProbe.weierstrassDiscriminantFormal_eq_deltaFormal]

/-- The concrete Tate-parameter map is a left inverse to the Tate-curve j-invariant. -/
theorem tateParameter_tateCurve_j (q : kˣ) (hq : valuation k (q : k) < 1) :
    letI := WeierstrassCurve.isElliptic_tateCurve q hq
    WeierstrassCurve.tateParameter (WeierstrassCurve.tateCurve (q : k)).j = (q : k) := by
  letI := WeierstrassCurve.isElliptic_tateCurve q hq
  rw [WeierstrassCurve.tateParameter_eq,
    WeierstrassCurve.tateCurve_j_inv_eq_evalInt_weierstrassJInvFormal q hq,
    weierstrassJInvFormal_eq_jInv]
  exact evalInt_jInv_jInvReverse (q : k) hq

/-- Conversely, the Tate curve of the parameter extracted from a nonintegral j-invariant
has that same j-invariant. -/
theorem tateCurve_tateParameter_j {j : k} (hj : 1 < valuation k j) :
    let q := WeierstrassCurve.tateParameter j
    let qU : kˣ := Units.mk0 q (WeierstrassCurve.tateParameter_ne_zero hj)
    letI := WeierstrassCurve.isElliptic_tateCurve qU
      (WeierstrassCurve.valuation_tateParameter_lt_one hj)
    (WeierstrassCurve.tateCurve (qU : k)).j = j := by
  dsimp only
  let qU : kˣ := Units.mk0 (WeierstrassCurve.tateParameter j)
    (WeierstrassCurve.tateParameter_ne_zero hj)
  letI := WeierstrassCurve.isElliptic_tateCurve qU
    (WeierstrassCurve.valuation_tateParameter_lt_one hj)
  apply inv_inj.mp
  rw [WeierstrassCurve.tateCurve_j_inv_eq_evalInt_weierstrassJInvFormal qU
    (WeierstrassCurve.valuation_tateParameter_lt_one hj),
    weierstrassJInvFormal_eq_jInv]
  change TateCurve.evalInt (WeierstrassCurve.tateParameter j) TateCurve.jInv = j⁻¹
  rw [WeierstrassCurve.tateParameter_eq]
  exact evalInt_jInvReverse_jInv j⁻¹
    (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj)

#print axioms evalInt_subst
#print axioms evalInt_jInv_jInvReverse
#print axioms tateParameter_tateCurve_j
#print axioms tateCurve_tateParameter_j

end TateSubstitutionBridgeProbe
