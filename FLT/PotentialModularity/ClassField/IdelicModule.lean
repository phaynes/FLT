/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.PotentialModularity.ClassField.PrincipalIdeles
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The algebraic idelic module

This file defines the normalized idelic module, proves its product formula on principal ideles,
and constructs the norm-one idele quotient with its inherited T3 topology.

Continuity, surjectivity, compactness, reciprocity, and character globalization are outside this
bounded interface.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- Units of the finite adele ring, decomposed as a restricted product of local units. -/
noncomputable def finiteIdeleUnitsEquiv :
    (FiniteAdeleRing (𝓞 K) K)ˣ ≃*
      Πʳ (v : HeightOneSpectrum (𝓞 K)),
        [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] := by
  unfold FiniteAdeleRing
  exact RestrictedProduct.unitsEquiv (HeightOneSpectrum.adicCompletion K)

/-- The normalized local factor of a finite idele. -/
noncomputable def finiteIdeleFactor
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) : NNRealˣ :=
  Units.map (nnnormHom (α := HeightOneSpectrum.adicCompletion K v)).toMonoidHom
    ((finiteIdeleUnitsEquiv K a) v)

/-- The local norm factors of a finite idele are one away from finitely many places. -/
theorem finiteIdeleFactor_hasFiniteMulSupport
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    Function.HasFiniteMulSupport (finiteIdeleFactor K a) := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq]
  intro hval
  apply hv
  apply Units.ext
  change (nnnormHom _ : NNReal) = 1
  have hval' :
      Valued.v ((finiteIdeleUnitsEquiv K a v : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := by
    change Valued.v (a.1 v) = 1
    exact hval
  have hn :
      ‖((finiteIdeleUnitsEquiv K a) v :
          HeightOneSpectrum.adicCompletion K v)‖ = 1 := by
    rw [FinitePlace.norm_def, hval', map_one]
    rfl
  have hnn :
      ‖((finiteIdeleUnitsEquiv K a) v :
          HeightOneSpectrum.adicCompletion K v)‖₊ = 1 := by
    ext
    simpa using hn
  simpa using hnn

@[simp]
theorem finiteIdeleFactor_one (v : HeightOneSpectrum (𝓞 K)) :
    finiteIdeleFactor K 1 v = 1 := by
  change Units.map _ ((finiteIdeleUnitsEquiv K 1) v) = 1
  rw [map_one]
  change Units.map _ (1 : (v.adicCompletion K)ˣ) = 1
  exact map_one _

@[simp]
theorem finiteIdeleFactor_mul
    (a b : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteIdeleFactor K (a * b) v = finiteIdeleFactor K a v * finiteIdeleFactor K b v := by
  change Units.map _ ((finiteIdeleUnitsEquiv K (a * b)) v) =
    Units.map _ ((finiteIdeleUnitsEquiv K a) v) *
      Units.map _ ((finiteIdeleUnitsEquiv K b) v)
  rw [map_mul]
  change Units.map _
      ((finiteIdeleUnitsEquiv K a v) * (finiteIdeleUnitsEquiv K b v)) = _
  exact map_mul _ _ _

/-- The product of the normalized local factors of a finite idele. -/
noncomputable def finiteIdeleModule :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* NNRealˣ where
  toFun a := ∏ᶠ v, finiteIdeleFactor K a v
  map_one' := by
    simp_rw [finiteIdeleFactor_one]
    exact finprod_one
  map_mul' a b := by
    simp_rw [finiteIdeleFactor_mul]
    exact
      finprod_mul_distrib (finiteIdeleFactor_hasFiniteMulSupport K a)
        (finiteIdeleFactor_hasFiniteMulSupport K b)

/-- Units of the infinite adele ring, decomposed coordinatewise. -/
noncomputable def infiniteIdeleUnitsEquiv :
    (InfiniteAdeleRing K)ˣ ≃* (∀ w : InfinitePlace K, w.Completionˣ) := by
  unfold InfiniteAdeleRing
  exact MulEquiv.piUnits

/-- The product of normalized archimedean local factors. -/
noncomputable def infiniteIdeleModule :
    (InfiniteAdeleRing K)ˣ →* NNRealˣ :=
  (∏ w : InfinitePlace K,
      (powMonoidHom w.mult).comp
        ((Units.map (nnnormHom (α := w.Completion)).toMonoidHom).comp
          (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completionˣ) w))).comp
    (infiniteIdeleUnitsEquiv K).toMonoidHom

/-- The normalized idelic module, with its archimedean and finite factors kept explicit. -/
noncomputable def ideleModule :
    (AdeleRing (𝓞 K) K)ˣ →* NNRealˣ :=
  ((infiniteIdeleModule K).coprod (finiteIdeleModule K)).comp
    MulEquiv.prodUnits.toMonoidHom

/-- Reindex the finite-adele norm product by finite places. -/
theorem finite_part (x : K) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖)
      = ∏ᶠ w : FinitePlace K, w x := by
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ = ‖FinitePlace.embedding v x‖ :=
    fun v => rfl
  simp only [hcoord]
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))
        (f := fun v => ‖FinitePlace.embedding v x‖)]
  exact finprod_congr fun w => FinitePlace.norm_embedding_eq w x

/-- The norm of a principal adele at an infinite coordinate is its infinite-place absolute value. -/
theorem infinite_coord (x : K) (w : InfinitePlace K) :
    ‖(algebraMap K (AdeleRing (𝓞 K) K) x).1 w‖ = w x := by
  simpa using InfinitePlace.Completion.norm_coe (v := w) ((WithAbs.equiv w.1).symm x)

/-- The real-valued product formula in the exact adele coordinates used by `ideleModule`. -/
theorem principal_product (x : K) (hx : x ≠ 0) :
    (∏ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) x).1 w‖ ^ w.mult)
      * (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            ‖(algebraMap K (AdeleRing (𝓞 K) K) x).2 v‖) = 1 := by
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(algebraMap K (AdeleRing (𝓞 K) K) x).2 v‖
        = ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ :=
    fun v => rfl
  simp only [infinite_coord, h2]
  rw [finite_part K x]
  exact prod_abs_eq_one hx

/-- The finite idelic module, transported from `NNRealˣ` to the real local-norm product. -/
theorem finiteIdeleModule_toReal
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (↑↑(finiteIdeleModule K a) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖((finiteIdeleUnitsEquiv K a v : (v.adicCompletion K)ˣ) :
          v.adicCompletion K)‖ := by
  change
    (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom NNReal))
      (∏ᶠ v, finiteIdeleFactor K a v) = _
  rw [MonoidHom.map_finprod _ (finiteIdeleFactor_hasFiniteMulSupport K a)]
  apply finprod_congr
  intro v
  rfl

/-- The infinite idelic module, transported from `NNRealˣ` to the real local-norm product. -/
theorem infiniteIdeleModule_toReal
    (a : (InfiniteAdeleRing K)ˣ) :
    (↑↑(infiniteIdeleModule K a) : ℝ) =
      ∏ w : InfinitePlace K,
        ‖((infiniteIdeleUnitsEquiv K a w : w.Completionˣ) : w.Completion)‖ ^ w.mult := by
  change
    (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom NNReal))
      ((∏ w : InfinitePlace K,
          (powMonoidHom w.mult).comp
            ((Units.map (nnnormHom (α := w.Completion)).toMonoidHom).comp
              (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completionˣ) w)))
        (infiniteIdeleUnitsEquiv K a)) = _
  rw [MonoidHom.finsetProd_apply]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro w _hw
  change
    (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom NNReal))
      ((Units.map (nnnormHom (α := w.Completion)).toMonoidHom
        (infiniteIdeleUnitsEquiv K a w)) ^ w.mult) = _
  rw [map_pow]
  change (↑‖((infiniteIdeleUnitsEquiv K a w : w.Completionˣ) : w.Completion)‖₊ : ℝ) ^
      w.mult =
    ‖((infiniteIdeleUnitsEquiv K a w : w.Completionˣ) : w.Completion)‖ ^ w.mult
  rw [coe_nnnorm]

/-- The normalized idelic module is one on every principal idele. -/
theorem ideleModule_principal (x : Kˣ) :
    ideleModule K
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x) = 1 := by
  apply Units.ext
  apply NNReal.coe_injective
  change
    (↑↑(ideleModule K
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x)) : ℝ) = 1
  change
    (↑↑(infiniteIdeleModule K
        (MulEquiv.prodUnits.toMonoidHom
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x)).1) : ℝ) *
      (↑↑(finiteIdeleModule K
        (MulEquiv.prodUnits.toMonoidHom
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom x)).2) : ℝ) = 1
  rw [infiniteIdeleModule_toReal, finiteIdeleModule_toReal]
  change
    (∏ w : InfinitePlace K,
        ‖(algebraMap K (AdeleRing (𝓞 K) K) (x : K)).1 w‖ ^ w.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖(algebraMap K (AdeleRing (𝓞 K) K) (x : K)).2 v‖) = 1
  exact principal_product K (x : K) x.ne_zero

/-- Every principal idele lies in the kernel of the normalized idelic module. -/
theorem principalIdeles_le_ideleModule_ker :
    principalIdeles K ≤ (ideleModule K).ker := by
  rintro y ⟨x, rfl⟩
  exact ideleModule_principal K x

/-- The normalized idelic module descended to the idele class group. -/
noncomputable def ideleClassModule : IdeleClassGroup K →* NNRealˣ :=
  QuotientGroup.lift (principalIdeles K) (ideleModule K)
    (principalIdeles_le_ideleModule_ker K)

/-- The subgroup of ideles with normalized module one. -/
noncomputable abbrev NormOneIdeles := (ideleModule K).ker

/-- Principal ideles regarded as a subgroup of the norm-one ideles. -/
noncomputable def principalNormOneIdeles : Subgroup (NormOneIdeles K) :=
  (principalIdeles K).comap (ideleModule K).ker.subtype

/-- The quotient of norm-one ideles by principal ideles. -/
noncomputable abbrev NormOneIdeleClassGroup :=
  NormOneIdeles K ⧸ principalNormOneIdeles K

/--
The kernel of the descended idelic module. This is intentionally distinct from
`NormOneIdeleClassGroup`; no equivalence between the two objects is established in this slice.
-/
noncomputable abbrev NormOneIdeleClassKernel := (ideleClassModule K).ker

/-- Principal norm-one ideles form a closed subgroup of the norm-one ideles. -/
theorem principalNormOneIdeles_isClosed :
    IsClosed ((principalNormOneIdeles K) : Set (NormOneIdeles K)) :=
  (principalIdeles_isClosed K).preimage continuous_subtype_val

/-- The norm-one idele class quotient inherits a regular Hausdorff topology. -/
instance instT3SpaceNormOneIdeleClassGroup : T3Space (NormOneIdeleClassGroup K) := by
  haveI := principalNormOneIdeles_isClosed K
  infer_instance

end FLT.PotentialModularity.ClassField
