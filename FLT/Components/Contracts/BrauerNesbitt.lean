/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Brauer--Nesbitt component contract

This module freezes the arbitrary-field group-representation contract used by the FLT programme and
banks its source-independent finite joint-image reduction. It does not prove the remaining
Brauer--Nesbitt terminal.

The contract deliberately retains equality of characteristic polynomials on every group element.
In positive characteristic, equality of traces alone is insufficient. The extracted finite basis
also consists of actual group elements; no invalid linear extension of characteristic polynomials
is used.
-/

@[expose] public section

namespace FLT.Components.BrauerNesbitt

/-- Semisimple finite-dimensional group representations with identical characteristic polynomials
on every group element are equivalent. This proposition is the component contract, not a proof of
the theorem. -/
def Contract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      (∀ g, (rho g).charpoly = (sigma g).charpoly) →
      Nonempty (Representation.Equiv rho sigma)

/-- Equality of characteristic polynomials supplies equality of traces. -/
theorem trace_eq_of_charpoly_eq
    {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : Module.End k V) (g : Module.End k W)
    (h : f.charpoly = g.charpoly) :
    LinearMap.trace k V f = LinearMap.trace k W g := by
  let bV := Module.Free.chooseBasis k V
  let bW := Module.Free.chooseBasis k W
  calc
    LinearMap.trace k V f = Matrix.trace (LinearMap.toMatrix bV bV f) :=
      LinearMap.trace_eq_matrix_trace k bV f
    _ = -(LinearMap.toMatrix bV bV f).charpoly.nextCoeff :=
      Matrix.trace_eq_neg_charpoly_nextCoeff _
    _ = -f.charpoly.nextCoeff := by rw [LinearMap.charpoly_toMatrix]
    _ = -g.charpoly.nextCoeff := by rw [h]
    _ = -(LinearMap.toMatrix bW bW g).charpoly.nextCoeff := by
      rw [LinearMap.charpoly_toMatrix]
    _ = Matrix.trace (LinearMap.toMatrix bW bW g) :=
      (Matrix.trace_eq_neg_charpoly_nextCoeff _).symm
    _ = LinearMap.trace k W g := (LinearMap.trace_eq_matrix_trace k bW g).symm

universe uK uG uV uW

section JointImage

variable {k : Type uK} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable (rho : Representation k G V) (sigma : Representation k G W)

/-- The pair of endomorphisms through which a group element acts. -/
def jointImagePoint (g : G) : Module.End k V × Module.End k W :=
  (rho g, sigma g)

/-- The finite-dimensional linear span of the joint group image. -/
def jointImageSpan : Submodule k (Module.End k V × Module.End k W) :=
  Submodule.span k (Set.range (jointImagePoint rho sigma))

/-- The joint-image span is closed under multiplication because the generators are a group image. -/
noncomputable def jointImageAlgebra : Subalgebra k (Module.End k V × Module.End k W) where
  carrier := jointImageSpan rho sigma
  zero_mem' := (jointImageSpan rho sigma).zero_mem
  add_mem' := (jointImageSpan rho sigma).add_mem
  one_mem' := by
    apply Submodule.subset_span
    exact ⟨1, by simp [jointImagePoint]⟩
  mul_mem' := by
    intro x y hx hy
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (jointImageSpan rho sigma) (Set.range (jointImagePoint rho sigma))
      (Set.range (jointImagePoint rho sigma))
      (LinearMap.mul k (Module.End k V × Module.End k W))
    · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      apply Submodule.subset_span
      exact ⟨g * h, by simp [jointImagePoint]⟩
    · exact hx
    · exact hy
  algebraMap_mem' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    exact (jointImageSpan rho sigma).smul_mem r (by
      apply Submodule.subset_span
      exact ⟨1, by simp [jointImagePoint]⟩)

/-- First projection of the joint-image algebra. -/
noncomputable def jointImageFst :
    jointImageAlgebra rho sigma →ₐ[k] Module.End k V :=
  (AlgHom.fst k (Module.End k V) (Module.End k W)).comp
    (jointImageAlgebra rho sigma).val

/-- Second projection of the joint-image algebra. -/
noncomputable def jointImageSnd :
    jointImageAlgebra rho sigma →ₐ[k] Module.End k W :=
  (AlgHom.snd k (Module.End k V) (Module.End k W)).comp
    (jointImageAlgebra rho sigma).val

/-- An actual group element embedded in the joint-image algebra. -/
noncomputable def jointImageElement (g : G) : jointImageAlgebra rho sigma :=
  ⟨jointImagePoint rho sigma g, Submodule.subset_span (Set.mem_range_self g)⟩

@[simp]
theorem jointImageFst_element (g : G) :
    jointImageFst rho sigma (jointImageElement rho sigma g) = rho g := rfl

@[simp]
theorem jointImageSnd_element (g : G) :
    jointImageSnd rho sigma (jointImageElement rho sigma g) = sigma g := rfl

theorem jointImageAlgebra_toSubmodule :
    (jointImageAlgebra rho sigma).toSubmodule = jointImageSpan rho sigma := rfl

variable [Module.Finite k V] [Module.Finite k W]

/-- A basis of the joint-image span selected from genuine group-image pairs. -/
theorem exists_jointImage_basis_from_group :
    ∃ g : Fin (Module.finrank k (jointImageSpan rho sigma)) → G,
      LinearIndependent k (fun i ↦ jointImagePoint rho sigma (g i)) ∧
        Submodule.span k (Set.range (fun i ↦ jointImagePoint rho sigma (g i))) =
          jointImageSpan rho sigma := by
  unfold jointImageSpan
  obtain ⟨f, hfS, hfspan, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq k
    (Set.range (jointImagePoint rho sigma))
  choose g hg using hfS
  have hgf : (fun i ↦ jointImagePoint rho sigma (g i)) = f := funext hg
  refine ⟨g, ?_, ?_⟩
  · rw [hgf]
    exact hfli
  · rw [hgf]
    exact hfspan

end JointImage

/-- Exact finite-dimensional remainder after the joint-image algebra and a basis of actual group
elements have been extracted. -/
def FiniteJointImageContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      (∀ g, (rho g).charpoly = (sigma g).charpoly) →
      ∀ (g : Fin (Module.finrank k (jointImageSpan rho sigma)) → G),
        LinearIndependent k (fun i ↦ jointImagePoint rho sigma (g i)) →
        Submodule.span k (Set.range (fun i ↦ jointImagePoint rho sigma (g i))) =
          jointImageSpan rho sigma →
        Nonempty (Representation.Equiv rho sigma)

/-- Proving the finite joint-image remainder proves the unchanged public contract. -/
theorem contract_of_finiteJointImageContract
    (hfinite : FiniteJointImageContract.{uK, uG, uV, uW}) :
    Contract.{uK, uG, uV, uW} := by
  intro k G V W _ _ _ _ _ _ _ _ rho sigma hrho hsigma hchar
  obtain ⟨g, hli, hspan⟩ := exists_jointImage_basis_from_group rho sigma
  exact hfinite rho sigma hrho hsigma hchar g hli hspan

end FLT.Components.BrauerNesbitt

end
