/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.PotentialModularity.ClassField.IdelicModuleTopology
public import Mathlib.Topology.Maps.Strict.Group

/-!
# Norm-one idele quotient/kernel comparison

This file identifies the quotient of norm-one ideles by principal ideles with the kernel of the
descended idelic module as a topological multiplicative group.

Compactness, reciprocity, globalization, parent closure, and promotion remain outside this bounded
interface.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

private theorem strictQuotientCompSubtype
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A P : Subgroup G) [P.Normal] (hPA : P ≤ A) :
    Topology.IsStrictMap
      ((QuotientGroup.mk' P).comp A.subtype : A →* G ⧸ P) := by
  rw [MonoidHom.isStrictMap_iff_isEmbedding_kerLift]
  apply isEmbedding_of_isOpenQuotientMap_of_isInducing
      (f := A.subtype)
      (g := QuotientGroup.kerLift
        ((QuotientGroup.mk' P).comp A.subtype))
      (p := QuotientGroup.mk'
        ((QuotientGroup.mk' P).comp A.subtype).ker)
      (q := QuotientGroup.mk' P)
  · rfl
  · exact Topology.IsInducing.subtypeVal
  · exact QuotientGroup.isQuotientMap_mk _
  · exact QuotientGroup.isOpenQuotientMap_mk
  · exact QuotientGroup.kerLift_injective _
  · rintro x ⟨_, ⟨a, rfl⟩, ha⟩
    have hxa : x / (a : G) ∈ P :=
      QuotientGroup.eq_iff_div_mem.mp ha.symm
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [← div_mul_cancel x (a : G)]
    exact A.mul_mem (hPA hxa) a.property

private noncomputable def quotientContinuousMulEquivOfEq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P Q : Subgroup G} [P.Normal] [Q.Normal] (h : P = Q) :
    G ⧸ P ≃ₜ* G ⧸ Q := by
  subst Q
  exact ContinuousMulEquiv.refl _

private noncomputable def subgroupContinuousMulEquivOfEq
    {G : Type*} [Group G] [TopologicalSpace G]
    {S T : Subgroup G} (h : S = T) :
    S ≃ₜ* T := by
  subst T
  exact ContinuousMulEquiv.refl _

/-- The class quotient map restricted to norm-one ideles. -/
public noncomputable def normOneIdelesToClass :
    NormOneIdeles K →ₜ* IdeleClassGroup K where
  __ := (QuotientGroup.mk' (principalIdeles K)).comp
    (NormOneIdeles K).subtype
  continuous_toFun :=
    QuotientGroup.continuous_mk.comp continuous_subtype_val

/-- The kernel of the restricted class quotient is the subgroup of principal norm-one ideles. -/
public theorem normOneIdelesToClass_ker :
    (normOneIdelesToClass K).ker = principalNormOneIdeles K := by
  ext x
  change
    (QuotientGroup.mk' (principalIdeles K)
        (x : (AdeleRing (𝓞 K) K)ˣ) = 1) ↔
      (x : (AdeleRing (𝓞 K) K)ˣ) ∈ principalIdeles K
  exact QuotientGroup.eq_one_iff (N := principalIdeles K) _

/-- The range of the restricted class quotient is the kernel of the descended idelic module. -/
public theorem normOneIdelesToClass_range :
    (normOneIdelesToClass K).range = NormOneIdeleClassKernel K := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change
      ideleClassModule K
          (QuotientGroup.mk' (principalIdeles K)
            (x : (AdeleRing (𝓞 K) K)ˣ)) = 1
    change ideleModule K (x : (AdeleRing (𝓞 K) K)ˣ) = 1
    exact x.property
  · intro hy
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (principalIdeles K) y
    change ideleModule K x = 1 at hy
    exact ⟨⟨x, hy⟩, rfl⟩

/-- The restricted class quotient map is strict. -/
public theorem normOneIdelesToClass_isStrictMap :
    Topology.IsStrictMap (normOneIdelesToClass K) := by
  change Topology.IsStrictMap
    ((QuotientGroup.mk' (principalIdeles K)).comp
      (NormOneIdeles K).subtype :
        NormOneIdeles K →* IdeleClassGroup K)
  exact strictQuotientCompSubtype
    (NormOneIdeles K) (principalIdeles K)
    (principalIdeles_le_ideleModule_ker K)

/-- The norm-one idele class quotient is topologically isomorphic to the class-module kernel. -/
public noncomputable def normOneIdeleClassQuotientEquivKernel :
    NormOneIdeleClassGroup K ≃ₜ* NormOneIdeleClassKernel K :=
  (quotientContinuousMulEquivOfEq
      (normOneIdelesToClass_ker K).symm).trans
    ((ContinuousMulEquiv.quotientKerEquivRange
        (normOneIdelesToClass_isStrictMap K)).trans
      (subgroupContinuousMulEquivOfEq
        (normOneIdelesToClass_range K)))

/-- Compactness of subsets is preserved and reflected by the quotient/kernel equivalence. -/
public theorem normOneIdeleClassQuotientEquivKernel_isCompact_image
    (s : Set (NormOneIdeleClassGroup K)) :
    IsCompact (normOneIdeleClassQuotientEquivKernel K '' s) ↔ IsCompact s :=
  (normOneIdeleClassQuotientEquivKernel K).toHomeomorph.isCompact_image

end FLT.PotentialModularity.ClassField
