/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FLTMethodology.Probes.TateReductionBridge
import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction

/-!
# Tate local-form classification boundary

This file gives exact Lean signatures for the remaining local-field form-classification
problem and proves that these signatures are sufficient to close the Tate-curve variable-change
construction. It does not assume or prove the two residual source theorems.
-/

open ValuativeRel

namespace TateLocalFormBoundaryProbe

universe u

/-- First residual source theorem: nonexceptional equal-j forms are either isomorphic or
a quadratic twist. -/
def SameJQuadraticFormClassification (k : Type u) [Field k] : Prop :=
  ∀ (E₁ E₂ : WeierstrassCurve k),
    ∀ (hE₁ : E₁.IsElliptic) (hE₂ : E₂.IsElliptic),
    letI := hE₁
    letI := hE₂
    E₂.j ≠ 0 → E₂.j ≠ 1728 → E₁.j = E₂.j →
      (∃ C : WeierstrassCurve.VariableChange k, C • E₁ = E₂) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (_ : Algebra.IsQuadraticExtension k L) (_ : Algebra.IsSeparable k L),
        ∃ C : WeierstrassCurve.VariableChange k, C • E₁ = E₂.quadraticTwist L

/-- Second residual source theorem: a nontrivial quadratic twist of a split-multiplicative
curve cannot be another split-multiplicative form. -/
def QuadraticTwistExcludesSecondSplit (k : Type u) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (E : WeierstrassCurve k) (L : Type u) [Field L] [Algebra k L]
    [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L],
    ∀ (hE : E.IsElliptic),
    letI := hE
    E.HasSplitMultiplicativeReduction 𝒪[k] →
      ∀ (E' : WeierstrassCurve k) (hE' : E'.IsElliptic),
      letI := hE'
      E'.HasSplitMultiplicativeReduction 𝒪[k] →
        ¬∃ C : WeierstrassCurve.VariableChange k, C • E' = E.quadraticTwist L

/-- The single interface consumed by the Tate variable-change constructor. -/
def LocalSplitSameJClassification (k : Type*) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (E₁ E₂ : WeierstrassCurve k),
    ∀ (hE₁ : E₁.IsElliptic) (hE₂ : E₂.IsElliptic),
    letI := hE₁
    letI := hE₂
    E₁.HasSplitMultiplicativeReduction 𝒪[k] →
    E₂.HasSplitMultiplicativeReduction 𝒪[k] →
    E₁.j = E₂.j →
    ∃ C : WeierstrassCurve.VariableChange k, C • E₁ = E₂

/-- The two residual boundaries imply the exact local split same-j classification. -/
theorem localSplitSameJClassification_of_quadraticBoundaries
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (hforms : SameJQuadraticFormClassification k)
    (hnot : QuadraticTwistExcludesSecondSplit k) :
    LocalSplitSameJClassification k := by
  intro E₁ E₂ hE₁ hE₂
  letI := hE₁
  letI := hE₂
  intro hsplit₁ hsplit₂ hj
  letI : E₁.HasSplitMultiplicativeReduction 𝒪[k] := hsplit₁
  letI : E₂.HasSplitMultiplicativeReduction 𝒪[k] := hsplit₂
  have hjgt : 1 < valuation k E₂.j := WeierstrassCurve.one_lt_valuation_j E₂
  have hj0 : E₂.j ≠ 0 := by
    intro h
    rw [h, map_zero] at hjgt
    exact (not_lt_of_ge zero_le) hjgt
  have hj1728 : E₂.j ≠ 1728 := by
    intro h
    rw [h] at hjgt
    exact (not_lt_of_ge (valuation_natCast_le_one 1728)) hjgt
  rcases hforms E₁ E₂ hE₁ hE₂ hj0 hj1728 hj with h | h
  · exact h
  · obtain ⟨L, _, _, _, _, C, hC⟩ := h
    exact (hnot E₂ L hE₂ hsplit₂ E₁ hE₁ hsplit₁ ⟨C, hC⟩).elim

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (E : WeierstrassCurve k) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]

/-- Once the exact local classification is supplied, the admitted provider theorem follows
without any further mathematics. -/
theorem exists_variableChange_tateCurve_of_localSplitSameJClassification
    (hclass : LocalSplitSameJClassification k) :
    ∃ C : WeierstrassCurve.VariableChange k,
      C • WeierstrassCurve.tateCurve E.q = E := by
  let qU : kˣ := Units.mk0 E.q E.q_ne_zero
  have hq : valuation k (qU : k) < 1 := by
    simpa [qU] using E.valuation_q_lt_one
  have hTateEll : (WeierstrassCurve.tateCurve (qU : k)).IsElliptic :=
    WeierstrassCurve.isElliptic_tateCurve qU hq
  have hTateSplit :
      (WeierstrassCurve.tateCurve (qU : k)).HasSplitMultiplicativeReduction 𝒪[k] :=
    TateReductionProbe.tateCurve_hasSplitMultiplicativeReduction qU hq
  have hSameJ : (WeierstrassCurve.tateCurve (qU : k)).j = E.j := by
    simpa [qU, WeierstrassCurve.q] using
      (TateSubstitutionBridgeProbe.tateCurve_tateParameter_j E.one_lt_valuation_j)
  simpa [qU] using hclass _ E hTateEll (inferInstance : E.IsElliptic)
    hTateSplit (inferInstance : E.HasSplitMultiplicativeReduction 𝒪[k]) hSameJ

#check WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist
#check WeierstrassCurve.not_exists_smul_quadraticTwist_eq
#print axioms localSplitSameJClassification_of_quadraticBoundaries
#print axioms exists_variableChange_tateCurve_of_localSplitSameJClassification

end TateLocalFormBoundaryProbe
