/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.GlobalLanglandsConjectures.GLnDefs

public import FLT.AutomorphicForm.GroupTheoryStuff
public import FLT.AutomorphicForm.Stuff
public import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import FLT.NumberField.Completion.Finite
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# A compact open subgroup of `GLₙ` over the finite adeles of `ℚ`

The existing quaternionic infrastructure constructs this subgroup for `GL₂`.  The restricted
product equivalence used there is dimension-generic, so this file records the corresponding
construction for an arbitrary finite matrix index.  It supplies the finite-level condition for
constant automorphic forms.
-/

@[expose] public section

open IsDedekindDomain RestrictedProduct

namespace AutomorphicForm.GLn.FiniteAdele

variable (m : Type*) [Fintype m] [DecidableEq m]

/-- Integral matrices at the finite place `v`. -/
noncomputable def matrixLocalFullLevel (v : HeightOneSpectrum ℤ) :
    Subring (Matrix m m (v.adicCompletion ℚ)) :=
  (v.adicCompletionIntegers ℚ).matrix

/-- Invertible integral matrices at the finite place `v`. -/
noncomputable def localFullLevel (v : HeightOneSpectrum ℤ) :
    Subgroup (GL m (v.adicCompletion ℚ)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers ℚ).subtype).toMonoidHom)

theorem matrixLocalFullLevel_isOpen (v : HeightOneSpectrum ℤ) :
    IsOpen (X := Matrix m m (v.adicCompletion ℚ)) (matrixLocalFullLevel m v) :=
  (Valued.isOpen_valuationSubring (v.adicCompletion ℚ)).matrix

theorem matrixLocalFullLevel_isCompact (v : HeightOneSpectrum ℤ) :
    IsCompact (X := Matrix m m (v.adicCompletion ℚ)) (matrixLocalFullLevel m v) := by
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).prop⟩
  let e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    (R := ℤ) v).symm.toHomeomorph
  letI : CompactSpace (v.adicCompletionIntegers ℚ) := e.compactSpace
  exact (isCompact_iff_compactSpace.mpr inferInstance).matrix

@[simp]
lemma units_matrixLocalFullLevel (v : HeightOneSpectrum ℤ) :
    (matrixLocalFullLevel m v).units = localFullLevel m v := by
  simp only [matrixLocalFullLevel, ← Units.range_map_subtype, localFullLevel]
  rw [← MonoidHom.range_comp_mulEquiv
    (Units.mapEquiv (Subring.matrixEquiv
      (v.adicCompletionIntegers ℚ).toSubring (n := m)).toMulEquiv)]
  rfl

theorem localFullLevel_isOpen (v : HeightOneSpectrum ℤ) :
    IsOpen (X := GL m (v.adicCompletion ℚ)) (localFullLevel m v) :=
  units_matrixLocalFullLevel m v ▸
    Submonoid.isOpen_units (matrixLocalFullLevel_isOpen m v)

theorem localFullLevel_isCompact (v : HeightOneSpectrum ℤ) :
    IsCompact (X := GL m (v.adicCompletion ℚ)) (localFullLevel m v) :=
  units_matrixLocalFullLevel m v ▸
    Submonoid.units_isCompact (matrixLocalFullLevel_isCompact m v)

/-- The local evaluation of the finite adele ring at `v`. -/
noncomputable def finiteAdeleToAdicCompletion (v : HeightOneSpectrum ℤ) :
    FiniteAdeleRing ℤ ℚ →ₐ[ℚ] v.adicCompletion ℚ where
  __ := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

/-- The local evaluation of `GLₙ` at `v`. -/
noncomputable def toAdicCompletion (v : HeightOneSpectrum ℤ) :
    GL m (FiniteAdeleRing ℤ ℚ) →* GL m (v.adicCompletion ℚ) :=
  Units.map (RingHom.mapMatrix
    (finiteAdeleToAdicCompletion v)).toMonoidHom

/-- `GLₙ(𝔸_ℚ^∞)` as a restricted product of the local general linear groups. -/
noncomputable def restrictedProduct :
    GL m (FiniteAdeleRing ℤ ℚ) ≃ₜ*
      Πʳ (v : HeightOneSpectrum ℤ),
        [GL m (v.adicCompletion ℚ), (matrixLocalFullLevel m v).units] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits
    (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

@[simp]
lemma restrictedProduct_apply (x : GL m (FiniteAdeleRing ℤ ℚ))
    (v : HeightOneSpectrum ℤ) :
    restrictedProduct m x v = toAdicCompletion m v x := rfl

/-- The standard maximal compact subgroup `∏ₚ GLₙ(ℤₚ)`. -/
noncomputable def maximalCompact : Subgroup (GL m (FiniteAdeleRing ℤ ℚ)) :=
  ⨅ v, (localFullLevel m v).comap (toAdicCompletion m v)

theorem maximalCompact_isOpen :
    IsOpen (X := GL m (FiniteAdeleRing ℤ ℚ)) (maximalCompact m) := by
  classical
  rw [← (restrictedProduct m).toHomeomorph.symm.isOpen_preimage]
  convert! RestrictedProduct.isOpen_forall_mem _ using 1
  · ext
    simp [maximalCompact, ← restrictedProduct_apply]
    rfl
  · exact fun v ↦ units_matrixLocalFullLevel m v ▸ localFullLevel_isOpen m v

theorem maximalCompact_isCompact :
    IsCompact (X := GL m (FiniteAdeleRing ℤ ℚ)) (maximalCompact m) := by
  classical
  rw [← (restrictedProduct m).toHomeomorph.symm.isCompact_preimage]
  convert! RestrictedProduct.isCompact_forall_mem_of_eventually_subset _
    (localFullLevel m) (localFullLevel_isCompact m) _ using 1
  · ext
    simp [maximalCompact, ← restrictedProduct_apply]
  · exact fun v ↦ units_matrixLocalFullLevel m v ▸ localFullLevel_isOpen m v
  · simp [units_matrixLocalFullLevel]

/-- A constant function has finite level, using the standard maximal compact subgroup. -/
theorem constant_has_finite_level {n : ℕ} (z : ℂ) :
    ∃ U, IsConstantOn U
      (fun _ : GL (Fin n) (FiniteAdeleRing ℤ ℚ) × GL (Fin n) ℝ ↦ z) := by
  refine ⟨maximalCompact (Fin n), maximalCompact_isOpen (Fin n),
    maximalCompact_isCompact (Fin n), ?_⟩
  simp

end AutomorphicForm.GLn.FiniteAdele
