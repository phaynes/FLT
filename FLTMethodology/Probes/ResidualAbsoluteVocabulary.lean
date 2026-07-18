import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Deformations.RepresentationTheory.Irreducible
import FLT.Slop.RepresentationTheory.OddAbsIrredSlop
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
Neutral residual-closure absolute-irreducibility vocabulary for the Taylor-2018
modularity-lifting source boundary (`FLT-ABSIRRED-VOCAB`).

This file provides only definitions. It states two residual-closure absolute-irreducibility
predicates and one open provider contract. Absolute irreducibility is tested in the common residual
closure `AlgebraicClosure (ZMod ell)` via an explicit coefficient embedding, going through
`GaloisRep.toRepresentation` and `Representation.baseChange` (both topology-free).

`ClosureImpliesClassAbsIrred` names the implication from the residual-closure form to the repository
`∀`-extension class `Representation.IsAbsolutelyIrreducible`. The theorem
`closureImpliesClassAbsIrred` proves that contract by Burnside/Schur density over the algebraically
closed residual field, faithful scalar descent of the full image algebra, and scalar extension of
that algebra to every coefficient field.
-/

namespace FLTMethodology.Taylor2018

open scoped TensorProduct

universe uG uK uk uW

/-- Absolute irreducibility of a residual representation, tested in the common residual closure
`AlgebraicClosure (ZMod ell)` via an explicit coefficient embedding `f`. -/
def IsAbsolutelyIrreducibleInResidualClosure
    {K : Type*} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) : Prop :=
  letI := f.toAlgebra
  Representation.IsIrreducible
    (Representation.baseChange (AlgebraicClosure (ZMod ell)) ρbar.toRepresentation)

/-- H4 target: restrict the *same* selected residual model to `F(ζ_ell)` FIRST, then test absolute
irreducibility in the residual closure. Dihedral representations are irreducible over `F` yet
reducible over `F(ζ_ell)`, so the restriction must precede the test. -/
def IsCyclotomicAbsolutelyIrreducibleInResidualClosure
    {F : Type*} [Field F] [NumberField F]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep F k W) : Prop :=
  IsAbsolutelyIrreducibleInResidualClosure ell f
    (ρbar.map (algebraMap F (CyclotomicField ell F)))

/-- PROVIDER CONTRACT (statement only; the first residual goal). Closure-form absolute
irreducibility in the residual closure ⇒ the repository `∀`-extension class
`Representation.IsAbsolutelyIrreducible` consumed by `Deformation.Representable`.
The theorem `closureImpliesClassAbsIrred` below discharges this provider. -/
def ClosureImpliesClassAbsIrred
    {K : Type uK} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) : Prop :=
  IsAbsolutelyIrreducibleInResidualClosure ell f ρbar →
    Representation.IsAbsolutelyIrreducible.{max uK uk uW, uK, uk, uW} ρbar.toRepresentation

/-! ## Closure-to-class bridge -/

/-- Over an algebraically closed field, an irreducible finite-dimensional representation generates
the full endomorphism algebra. This is the Burnside/Schur density step used by the residual
bridge. -/
lemma adjoinRange_eq_top_of_isAlgClosed_irreducible
    {G : Type uG} [Group G]
    {k : Type uk} [Field k] [IsAlgClosed k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (ρ : Representation k G W) (hirr : Representation.IsIrreducible ρ) :
    Slop.OddRep.adjoinRange ρ = ⊤ := by
  apply Slop.OddRep.adjoinRange_eq_top ρ hirr
  intro T hT
  let A := Slop.OddRep.adjoinRange ρ
  have hmem : ∀ g : G, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  haveI : IsScalarTower k A W := ⟨fun _ _ _ => rfl⟩
  haveI : IsSimpleModule A W := by
    have hnt : Nontrivial W := (Slop.OddRep.isIrreducible_iff_forall ρ).mp hirr |>.1
    letI : Nontrivial W := hnt
    haveI := (Submodule.nontrivial_iff A).mpr hnt
    rw [isSimpleModule_iff]
    refine ⟨fun U => ?_⟩
    have hU : ∀ g : G, ∀ w ∈ U.restrictScalars k, ρ g w ∈ U.restrictScalars k :=
      fun g w hw => U.smul_mem ⟨ρ g, hmem g⟩ hw
    simpa only [Submodule.restrictScalars_eq_bot_iff, Submodule.restrictScalars_eq_top_iff]
      using (Slop.OddRep.isIrreducible_iff_forall ρ).mp hirr |>.2 _ hU
  have hcommA : ∀ a : A, Commute (a : Module.End k W) T := by
    intro a
    have aux : ∀ x : Module.End k W, x ∈ Algebra.adjoin k (Set.range ρ) → Commute x T := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          obtain ⟨g, rfl⟩ := hx
          exact hT g
      | algebraMap r =>
          apply LinearMap.ext
          intro w
          change r • T w = T (r • w)
          rw [T.map_smul]
      | add x y _ _ hx hy => exact hx.add_left hy
      | mul x y _ _ hx hy => exact hx.mul_left hy
    exact aux a a.property
  let TA : Module.End A W :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun a w => by
        exact (LinearMap.congr_fun (hcommA a).eq w).symm }
  obtain ⟨μ, hμ⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := W)).2 TA
  refine ⟨μ, LinearMap.ext fun w => ?_⟩
  have hw := LinearMap.congr_fun hμ w
  simpa [TA, Module.algebraMap_end_apply] using hw.symm

/-- Fullness of the image algebra descends along a field extension. The proof tensors the base
image algebra into the extension field, maps it onto the full extended endomorphism algebra, and
compares finite dimensions. -/
lemma adjoinRange_eq_top_of_baseChange_eq_top
    {G : Type uG} [Group G]
    {k : Type uk} [Field k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (ρ : Representation k G W)
    (l : Type*) [Field l] [Algebra k l]
    (hbc : Slop.OddRep.adjoinRange (Slop.OddRep.baseChange l ρ) = ⊤) :
    Slop.OddRep.adjoinRange ρ = ⊤ := by
  classical
  let A := Slop.OddRep.adjoinRange ρ
  let φ : l ⊗[k] A →ₐ[l] Module.End l (l ⊗[k] W) :=
    (LinearMap.tensorProductEnd k l W).comp
      (Algebra.TensorProduct.map (AlgHom.id l l) A.val)
  have hgen : ∀ g : G, Slop.OddRep.baseChange l ρ g ∈ φ.range := by
    intro g
    refine ⟨1 ⊗ₜ[k] (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : A), ?_⟩
    change φ (1 ⊗ₜ[k] (⟨ρ g, _⟩ : A)) = LinearMap.baseChange l (ρ g)
    simp [φ, LinearMap.tensorProductEnd, LinearMap.tensorProduct]
  have hsurj : Function.Surjective φ := by
    apply (AlgHom.range_eq_top φ).mp
    apply le_antisymm le_top
    rw [← hbc, Slop.OddRep.adjoinRange]
    apply Algebra.adjoin_le
    rintro _ ⟨g, rfl⟩
    exact hgen g
  have hdim : Module.finrank k (Module.End k W) ≤ Module.finrank k A := by
    calc
      Module.finrank k (Module.End k W) =
          Module.finrank l (Module.End l (l ⊗[k] W)) := by
            simp [Module.finrank_linearMap]
      _ ≤ Module.finrank l (l ⊗[k] A) :=
        LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj
      _ = Module.finrank k A := Module.finrank_baseChange
  rw [← Algebra.toSubmodule_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le A.toSubmodule) hdim

/-- Irreducibility after base change to the chosen residual algebraic closure implies the repository
class asserting irreducibility after every field extension. -/
theorem closureImpliesClassAbsIrred
    {K : Type uK} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) :
    ClosureImpliesClassAbsIrred ell f ρbar := by
  intro hclosure
  let L := AlgebraicClosure (ZMod ell)
  letI : Algebra k L := f.toAlgebra
  let ρ := ρbar.toRepresentation
  have hclosure' : (Slop.OddRep.baseChange L ρ).IsIrreducible := by
    simpa [L, ρ, Slop.OddRep.baseChange, Representation.baseChange,
      IsAbsolutelyIrreducibleInResidualClosure] using hclosure
  have hLtop : Slop.OddRep.adjoinRange (Slop.OddRep.baseChange L ρ) = ⊤ :=
    adjoinRange_eq_top_of_isAlgClosed_irreducible _ hclosure'
  have hktop : Slop.OddRep.adjoinRange ρ = ⊤ :=
    adjoinRange_eq_top_of_baseChange_eq_top ρ L hLtop
  have hirr : ρ.IsIrreducible :=
    Slop.OddRep.isIrreducible_of_baseChange ρ L hclosure'
  have hnt : Nontrivial W := (Slop.OddRep.isIrreducible_iff_forall ρ).mp hirr |>.1
  letI : Nontrivial W := hnt
  constructor
  intro k' _ _
  have hktop' : Slop.OddRep.adjoinRange (Slop.OddRep.baseChange k' ρ) = ⊤ :=
    Slop.OddRep.adjoinRange_baseChange_eq_top ρ k' hktop
  obtain ⟨w, hw0⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hw0
  have hne : (1 : k') ⊗ₜ[k] w ≠ 0 := by
    intro hzero
    have hcontra := congrArg
      (fun t => (TensorProduct.rid k k').toLinearMap (LinearMap.lTensor k' φ t)) hzero
    simp only [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, hφ,
      one_smul, map_zero] at hcontra
    exact one_ne_zero hcontra
  letI : Nontrivial (k' ⊗[k] W) := nontrivial_of_ne _ _ hne
  have hirr' := Slop.OddRep.isIrreducible_of_adjoinRange_eq_top
    (Slop.OddRep.baseChange k' ρ) hktop'
  simpa [ρ, Slop.OddRep.baseChange, Representation.baseChange] using hirr'

end FLTMethodology.Taylor2018
