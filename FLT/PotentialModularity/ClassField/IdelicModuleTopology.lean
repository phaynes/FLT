/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.PotentialModularity.ClassField.IdelicModule
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import FLT.NumberField.Completion.Finite

/-!
# Topology of the idelic module

This file proves continuity of the normalized idelic module and its descent to the idele class
group, then records closedness of their norm-one kernels.

Compactness, quotient-kernel comparison, reciprocity, and globalization remain outside this bounded
interface.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- The finite idelic module is continuous for the restricted-product topology. -/
theorem finiteIdeleModule_continuous : Continuous (finiteIdeleModule K) := by
  let e :
      (FiniteAdeleRing (𝓞 K) K)ˣ ≃ₜ*
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [(v.adicCompletion K)ˣ,
            (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
    ContinuousMulEquiv.restrictedProductUnits
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
      (fun v => isOpenAdicCompletionIntegers K v)
  let f :
      (Πʳ v : HeightOneSpectrum (𝓞 K),
        [(v.adicCompletion K)ˣ,
          (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) → NNRealˣ :=
    fun a => ∏ᶠ v,
      Units.map (nnnormHom (α := v.adicCompletion K)).toMonoidHom (a v)
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_dom]
    intro S hS
    have hSc : Sᶜ.Finite := by
      rw [Filter.le_principal_iff] at hS
      exact hS
    have h_support :
        ∀ a : Πʳ v : HeightOneSpectrum (𝓞 K),
            [(v.adicCompletion K)ˣ,
              (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[Filter.principal S],
          Function.mulSupport
            (fun v => Units.map
              (nnnormHom (α := v.adicCompletion K)).toMonoidHom
              ((RestrictedProduct.inclusion _ _ hS a) v)) ⊆ Sᶜ := by
      intro a v hv
      by_contra hvSc
      have hvS : v ∈ S := by simpa [Set.mem_compl_iff] using hvSc
      have hv_mem : a v ∈
          (Submonoid.ofClass (v.adicCompletionIntegers K)).units :=
        a.property hvS
      have hv_val :
          Valued.v ((a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (v := v) (a := a v)).mp hv_mem
      have hn :
          ‖((a v : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
        rw [FinitePlace.norm_def, hv_val, map_one]
        rfl
      have hnn :
          ‖((a v : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ = 1 := by
        ext
        simpa using hn
      apply hv
      apply Units.ext
      change (nnnormHom _ : NNReal) = 1
      simpa using hnn
    have h_eq :
        (f ∘ RestrictedProduct.inclusion
          (fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletion K)ˣ)
          (fun v => (Submonoid.ofClass
            (v.adicCompletionIntegers K)).units) hS) =
          fun a => ∏ v ∈ hSc.toFinset,
            Units.map (nnnormHom (α := v.adicCompletion K)).toMonoidHom (a v) := by
      funext a
      change (∏ᶠ v,
        Units.map (nnnormHom (α := v.adicCompletion K)).toMonoidHom
          ((RestrictedProduct.inclusion _ _ hS a) v)) = _
      rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (h_support a) hSc]
      rfl
    rw [h_eq]
    exact continuous_finsetProd _ fun v _ =>
      (Units.continuous_map continuous_nnnorm).comp
        (RestrictedProduct.continuous_eval v)
  exact hf.comp e.continuous_toFun

/-- The archimedean idelic module is continuous as a finite product of coordinate norms. -/
theorem infiniteIdeleModule_continuous : Continuous (infiniteIdeleModule K) := by
  have hfun : (infiniteIdeleModule K :
      (InfiniteAdeleRing K)ˣ → NNRealˣ) =
      fun a => ∏ w,
        (Units.map (nnnormHom (α := w.Completion)).toMonoidHom
          ((infiniteIdeleUnitsEquiv K a) w)) ^ w.mult := by
    funext a
    simp only [infiniteIdeleModule, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.finsetProd_apply, powMonoidHom_apply]
    apply Finset.prod_congr rfl
    intro w _
    rfl
  rw [hfun]
  exact continuous_finsetProd _ fun w _ =>
    ((Units.continuous_map continuous_nnnorm).comp
      ((continuous_apply w).comp
        ContinuousMulEquiv.piUnits.continuous_toFun)).pow w.mult

/-- The normalized idelic module is continuous. -/
theorem ideleModule_continuous : Continuous (ideleModule K) := by
  have hprod : Continuous
      (MulEquiv.prodUnits :
        (AdeleRing (𝓞 K) K)ˣ →
          (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    apply continuous_prodMk.mpr
    exact ⟨Units.continuous_map continuous_fst,
      Units.continuous_map continuous_snd⟩
  have hfactor :
      Continuous (fun a :
          (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ =>
        infiniteIdeleModule K a.1 * finiteIdeleModule K a.2) :=
    ((infiniteIdeleModule_continuous K).comp continuous_fst).mul
      ((finiteIdeleModule_continuous K).comp continuous_snd)
  have hfun : (ideleModule K : (AdeleRing (𝓞 K) K)ˣ → NNRealˣ) =
      fun a =>
        infiniteIdeleModule K (MulEquiv.prodUnits a).1 *
          finiteIdeleModule K (MulEquiv.prodUnits a).2 := by
    funext a
    simp only [ideleModule, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coprod_apply]
    rfl
  rw [hfun]
  exact hfactor.comp hprod

/-- The normalized idelic module descends continuously to the idele class group. -/
theorem ideleClassModule_continuous : Continuous (ideleClassModule K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (principalIdeles K)).continuous_iff.mpr
  convert ideleModule_continuous K using 1
  funext x
  exact QuotientGroup.lift_mk (principalIdeles K)
    (principalIdeles_le_ideleModule_ker K) x

/-- The norm-one ideles form a closed subset of the ideles. -/
theorem normOneIdeles_isClosed :
    IsClosed (NormOneIdeles K : Set (AdeleRing (𝓞 K) K)ˣ) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (ideleModule_continuous K)

/-- The kernel of the descended idelic module is closed in the idele class group. -/
theorem normOneIdeleClassKernel_isClosed :
    IsClosed (NormOneIdeleClassKernel K : Set (IdeleClassGroup K)) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (ideleClassModule_continuous K)

end FLT.PotentialModularity.ClassField
