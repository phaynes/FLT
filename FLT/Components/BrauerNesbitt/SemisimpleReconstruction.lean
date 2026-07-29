/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.AmitsurFinTwo
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Morita.Matrix
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Reconstructing semisimple modules from idempotent ranks

This module develops the arbitrary-field Wedderburn--Artin reconstruction used by the
Brauer--Nesbitt terminal.  It works with division-algebra blocks directly and therefore does not
pass to a splitting field.
-/

@[expose] public section

namespace FLT.Components.BrauerNesbitt

namespace PiBlocks

universe uI uR uM

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable (R : ι → Type uR) [∀ i, Ring (R i)]

/-- The central idempotent selecting one factor of a finite product of rings. -/
def coordinateIdempotent (i : ι) : (∀ j, R j) := Pi.single i 1

@[simp]
theorem coordinateIdempotent_apply_same (i : ι) : coordinateIdempotent R i i = 1 :=
  Pi.single_eq_same i 1

@[simp]
theorem coordinateIdempotent_apply_of_ne {i j : ι} (h : j ≠ i) :
    coordinateIdempotent R i j = 0 := Pi.single_eq_of_ne h 1

theorem coordinateIdempotent_mul (i : ι) (r : ∀ j, R j) :
    coordinateIdempotent R i * r = Pi.single i (r i) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, Pi.single_eq_of_ne h]

theorem mul_coordinateIdempotent (i : ι) (r : ∀ j, R j) :
    r * coordinateIdempotent R i = Pi.single i (r i) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, Pi.single_eq_of_ne h]

theorem coordinateIdempotent_comm (i : ι) (r : ∀ j, R j) :
    coordinateIdempotent R i * r = r * coordinateIdempotent R i := by
  rw [coordinateIdempotent_mul, mul_coordinateIdempotent]

theorem coordinateIdempotent_idem (i : ι) :
    IsIdempotentElem (coordinateIdempotent R i) := by
  rw [IsIdempotentElem, coordinateIdempotent_mul]
  simp [coordinateIdempotent]

theorem coordinateIdempotent_orthogonal {i j : ι} (h : i ≠ j) :
    coordinateIdempotent R i * coordinateIdempotent R j = 0 := by
  rw [coordinateIdempotent_mul]
  simp [coordinateIdempotent, Pi.single_eq_of_ne h]

theorem sum_coordinateIdempotent :
    ∑ i, coordinateIdempotent R i = 1 := by
  ext j
  simp [coordinateIdempotent]

variable {M : Type uM} [AddCommGroup M] [Module (∀ j, R j) M]

/-- Projection to one central block of a module over a finite product of rings. -/
def componentProjection (i : ι) : Module.End (∀ j, R j) M where
  toFun x := coordinateIdempotent R i • x
  map_add' x y := smul_add _ _ _
  map_smul' r x := by
    change coordinateIdempotent R i • (r • x) = r • (coordinateIdempotent R i • x)
    rw [← mul_smul, ← mul_smul, coordinateIdempotent_comm]

/-- The module component selected by one central coordinate idempotent. -/
def Component (i : ι) : Submodule (∀ j, R j) M :=
  LinearMap.range (componentProjection R i)

theorem componentProjection_idem (i : ι) :
    IsIdempotentElem (componentProjection (M := M) R i) := by
  rw [IsIdempotentElem]
  ext x
  change coordinateIdempotent R i • (coordinateIdempotent R i • x) =
    coordinateIdempotent R i • x
  rw [← mul_smul, (coordinateIdempotent_idem R i).eq]

@[simp]
theorem componentProjection_apply_component (i : ι) (x : Component (M := M) R i) :
    componentProjection (M := M) R i x.1 = x.1 := by
  rcases x.2 with ⟨y, hy⟩
  rw [← hy]
  exact congrArg (fun f : Module.End (∀ j, R j) M ↦ f y)
    (componentProjection_idem (M := M) R i).eq

/-- A block component is naturally a module over its selected coordinate ring. -/
scoped instance componentModule (i : ι) : Module (R i) (Component (M := M) R i) where
  smul r x := ⟨Pi.single i r • x.1, by
    refine ⟨Pi.single i r • x.1, ?_⟩
    change coordinateIdempotent R i • (Pi.single i r • x.1) = Pi.single i r • x.1
    rw [← mul_smul, coordinateIdempotent_mul]
    simp⟩
  one_smul x := by
    apply Subtype.ext
    change coordinateIdempotent R i • x.1 = x.1
    exact componentProjection_apply_component R i x
  mul_smul r s x := by
    apply Subtype.ext
    change Pi.single i (r * s) • x.1 = Pi.single i r • (Pi.single i s • x.1)
    rw [Pi.single_mul, mul_smul]
  smul_zero r := by apply Subtype.ext; exact smul_zero _
  smul_add r x y := by apply Subtype.ext; exact smul_add _ _ _
  add_smul r s x := by
    apply Subtype.ext
    change Pi.single i (r + s) • x.1 =
      Pi.single i r • x.1 + Pi.single i s • x.1
    rw [Pi.single_add, add_smul]
  zero_smul x := by
    apply Subtype.ext
    change Pi.single i (0 : R i) • x.1 = (0 : M)
    rw [Pi.single_zero, zero_smul]

/-- A module over a finite product is the product of the submodules selected by its central
coordinate idempotents. -/
def decompose : M ≃ₗ[(∀ j, R j)] ∀ i, Component (M := M) R i where
  toFun x i := ⟨componentProjection R i x, ⟨x, rfl⟩⟩
  map_add' x y := by
    ext i
    change componentProjection R i (x + y) =
      componentProjection R i x + componentProjection R i y
    exact map_add (componentProjection R i) x y
  map_smul' r x := by
    apply funext
    intro i
    apply Subtype.ext
    change coordinateIdempotent R i • (r • x) =
      Pi.single i (r i) • (coordinateIdempotent R i • x)
    rw [← mul_smul, ← mul_smul, coordinateIdempotent_mul, mul_coordinateIdempotent]
    simp
  invFun x := ∑ i, (x i).1
  left_inv x := by
    change (∑ i, coordinateIdempotent R i • x) = x
    rw [← Finset.sum_smul, sum_coordinateIdempotent, one_smul]
  right_inv x := by
    ext i
    change coordinateIdempotent R i • (∑ j, (x j).1) = (x i).1
    rw [Finset.smul_sum, Finset.sum_eq_single i]
    · exact componentProjection_apply_component R i (x i)
    · intro j _ hji
      rw [← componentProjection_apply_component R j (x j)]
      change coordinateIdempotent R i • (coordinateIdempotent R j • (x j).1) = 0
      rw [← mul_smul, coordinateIdempotent_orthogonal R hji.symm, zero_smul]
    · simp

/-- The action of a product ring on one central component uses only the corresponding
coordinate. -/
theorem smul_component_eq_coordinate_smul (i : ι) (r : ∀ j, R j)
    (x : Component (M := M) R i) :
    r • x = (r i) • x := by
  apply Subtype.ext
  change r • x.1 = Pi.single i (r i) • x.1
  rw [← componentProjection_apply_component R i x]
  change r • (coordinateIdempotent R i • x.1) =
    Pi.single i (r i) • (coordinateIdempotent R i • x.1)
  simp only [← mul_smul, mul_coordinateIdempotent]
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, Pi.single_eq_of_ne h]

variable {k : Type*} [CommSemiring k] [Algebra k (∀ j, R j)]
variable [Module k M] [IsScalarTower k (∀ j, R j) M]

/-- The central component, originally defined as the range of a product-linear projection, is
the same ground-module as the range of left scalar multiplication by the corresponding central
idempotent. -/
def componentEquivRangeLsmul (i : ι) :
    Component (M := M) R i ≃ₗ[k]
      LinearMap.range (Algebra.lsmul k k M (coordinateIdempotent R i)) where
  toFun x := ⟨x.1, by
    rcases x.2 with ⟨y, hy⟩
    exact ⟨y, hy⟩⟩
  invFun x := ⟨x.1, by
    rcases x.2 with ⟨y, hy⟩
    exact ⟨y, hy⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_component_eq_range_lsmul [Module.Finite k M] (i : ι) :
    Module.finrank k (Component (M := M) R i) =
      Module.finrank k
        (LinearMap.range (Algebra.lsmul k k M (coordinateIdempotent R i))) :=
  (componentEquivRangeLsmul (M := M) R i).finrank_eq

variable {N : Type*} [AddCommGroup N] [Module (∀ j, R j) N]

/-- A coordinate-linear equivalence is linear over the whole product ring because both component
actions factor through that coordinate. -/
def componentLinearEquivOverPi (i : ι)
    (e : Component (M := M) R i ≃ₗ[R i] Component (M := N) R i) :
    Component (M := M) R i ≃ₗ[(∀ j, R j)] Component (M := N) R i where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [smul_component_eq_coordinate_smul R i r x,
      smul_component_eq_coordinate_smul R i r (e x)]
    exact e.map_smul (r i) x

/-- Pointwise equivalences of central components assemble to an equivalence over the product
ring. -/
def componentwiseLinearEquiv
    (e : ∀ i, Component (M := M) R i ≃ₗ[R i] Component (M := N) R i) :
    (∀ i, Component (M := M) R i) ≃ₗ[(∀ j, R j)]
      ∀ i, Component (M := N) R i where
  toFun x i := e i (x i)
  invFun y i := (e i).symm (y i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv y := by
    funext i
    exact (e i).apply_symm_apply (y i)
  map_add' x y := by
    funext i
    exact (e i).map_add (x i) (y i)
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply', RingHom.id_apply]
    exact (e i).map_smul (r i) (x i)

end PiBlocks

namespace MatrixBlocks

universe uD uI uM uN

variable (D : Type uD) [DivisionRing D]
variable (ι : Type uI) [Fintype ι] [DecidableEq ι]
variable (M : Type uM) [AddCommGroup M] [Module (Matrix ι ι D) M]
variable (N : Type uN) [AddCommGroup N] [Module (Matrix ι ι D) N]
variable [Module D M] [IsScalarTower D (Matrix ι ι D) M]
variable [Module D N] [IsScalarTower D (Matrix ι ι D) N]

open scoped Matrix.Module

/-- Applying a linear equivalence pointwise gives a matrix-linear equivalence. -/
noncomputable def mapMatrixLinearEquiv {U : Type*} {V : Type*}
    [AddCommGroup U] [Module D U] [AddCommGroup V] [Module D V]
    (e : U ≃ₗ[D] V) : (ι → U) ≃ₗ[Matrix ι ι D] (ι → V) :=
  LinearEquiv.ofBijective (e.toLinearMap.mapMatrixModule ι) ⟨
    (fun f g h ↦ funext fun i ↦ e.injective (congrFun h i)),
    (fun g ↦ ⟨fun i ↦ e.symm (g i), funext fun i ↦ e.apply_symm_apply (g i)⟩)⟩

/-- The matrix Morita equivalence, stated using the ambient compatible scalar action. -/
def moritaLinearEquiv (j : ι) :
    M ≃ₗ[Matrix ι ι D] (ι → MatrixModCat.toModuleCatObj D M j) where
  toFun m i := ⟨Matrix.single j i (1 : D) • m, Matrix.single j i (1 : D) • m, by
    simp [← mul_smul]⟩
  map_add' _ _ := by ext; simp
  map_smul' x m := funext fun i ↦ Subtype.ext <| by
    simp only [← mul_smul, RingHom.id_apply, Matrix.Module.smul_apply,
      AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, ← smul_assoc, ← Finset.sum_smul]
    congr
    ext i1 j1
    simp only [Matrix.mul_apply, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_apply]
    rw [Finset.sum_eq_single_of_mem (a := i) (by simp)
      (fun b _ hb ↦ by simp [Matrix.single, Ne.symm hb])]
    by_cases h : j = i1
    · subst i1
      simp [Matrix.single_apply]
    · simp [Matrix.single_apply, h]
  invFun m := ∑ i, Matrix.single i j (1 : D) • m i
  left_inv m := by simp [← mul_smul, ← Finset.sum_smul, Matrix.sum_single_one]
  right_inv v := by
    dsimp
    ext i
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single i (fun b _ hb ↦ by
      simp [← mul_smul, Matrix.single_mul_single_of_ne _ _ _ _ hb.symm]) (by simp)]
    obtain ⟨y, hy⟩ := by simpa [-SetLike.coe_mem] using (v i).2
    simp [← mul_smul, ← hy]

/-- Finite modules over a full matrix algebra over a division ring are determined by their
dimension over that division ring. -/
theorem nonempty_linearEquiv_of_finrank_eq
    [Module.Finite D M] [Module.Finite D N] (j : ι)
    (h : Module.finrank D M = Module.finrank D N) :
    Nonempty (M ≃ₗ[Matrix ι ι D] N) := by
  let EM := moritaLinearEquiv D ι M j
  let EN := moritaLinearEquiv D ι N j
  let UM := MatrixModCat.toModuleCatObj D M j
  let UN := MatrixModCat.toModuleCatObj D N j
  letI : Module.Finite D UM := by
    dsimp [UM, MatrixModCat.toModuleCatObj]
    exact Module.Finite.range _
  letI : Module.Finite D UN := by
    dsimp [UN, MatrixModCat.toModuleCatObj]
    exact Module.Finite.range _
  have hM : Module.finrank D M = Fintype.card ι * Module.finrank D UM := by
    rw [(EM.restrictScalars D).finrank_eq, Module.finrank_pi_fintype]
    dsimp [UM]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hN : Module.finrank D N = Fintype.card ι * Module.finrank D UN := by
    rw [(EN.restrictScalars D).finrank_eq, Module.finrank_pi_fintype]
    dsimp [UN]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hcorner : Module.finrank D UM = Module.finrank D UN := by
    apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.mpr ⟨j⟩)
    rw [← hM, h, hN]
  let e := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hcorner).some
  exact ⟨EM.trans ((mapMatrixLinearEquiv D ι e).trans EN.symm)⟩

/-- The same reconstruction criterion measured over a central ground field. -/
theorem nonempty_linearEquiv_of_restrictScalars_finrank_eq
    {k : Type*} [Field k] [Algebra k D] [Module.Finite k D]
    [Module k M] [Module k N] [Module.Finite k M] [Module.Finite k N]
    [IsScalarTower k D M] [IsScalarTower k D N] (j : ι)
    (h : Module.finrank k M = Module.finrank k N) :
    Nonempty (M ≃ₗ[Matrix ι ι D] N) := by
  letI : Module.Finite D M := Module.Finite.of_restrictScalars_finite k D M
  letI : Module.Finite D N := Module.Finite.of_restrictScalars_finite k D N
  apply nonempty_linearEquiv_of_finrank_eq D ι M N j
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := D))
  rw [Module.finrank_mul_finrank k D M, Module.finrank_mul_finrank k D N, h]

end MatrixBlocks

namespace PiMatrixBlocks

universe uK uI uD uM uN

variable (k : Type uK) [Field k]
variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable (D : ι → Type uD) [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
variable [∀ i, Module.Finite k (D i)]
variable (d : ι → ℕ) [∀ i, NeZero (d i)]

abbrev Block (i : ι) := Matrix (Fin (d i)) (Fin (d i)) (D i)
abbrev AlgebraPi := ∀ i, Block D d i

variable {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
variable [Module (AlgebraPi D d) M] [IsScalarTower k (AlgebraPi D d) M]
variable {N : Type uN} [AddCommGroup N] [Module k N] [Module.Finite k N]
variable [Module (AlgebraPi D d) N] [IsScalarTower k (AlgebraPi D d) N]

open scoped PiBlocks

local instance componentBlockModule (i : ι) :
    Module (Block D d i) (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
  PiBlocks.componentModule (fun i ↦ Block D d i) i

scoped instance componentDivisionModule (i : ι) :
    Module (D i) (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
  Module.compHom _ (Matrix.scalar (Fin (d i)))

theorem algebraMap_mul_coordinateIdempotent (r : k) (i : ι) :
    algebraMap k (AlgebraPi D d) r *
      PiBlocks.coordinateIdempotent (fun i ↦ Block D d i) i =
        Pi.single i (Matrix.scalar (Fin (d i)) (algebraMap k (D i) r)) := by
  rw [PiBlocks.mul_coordinateIdempotent]
  congr 1

/-- The ground-field action on a product component factors through the division algebra in its
matrix block. -/
theorem component_smul_assoc (i : ι) (r : k) (s : D i)
    (x : PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :
    (r • s) • x = r • (s • x) := by
  apply Subtype.ext
  change (Pi.single i (Matrix.scalar (Fin (d i)) (r • s)) :
      AlgebraPi D d) • x.1 =
    r • ((Pi.single i (Matrix.scalar (Fin (d i)) s) : AlgebraPi D d) • x.1)
  rw [← smul_assoc]
  congr 1
  ext j a b
  by_cases h : j = i
  · subst j
    by_cases hab : a = b
    · subst b
      simp [Algebra.smul_def, Matrix.scalar_apply]
    · simp [Algebra.smul_def, Matrix.scalar_apply, Matrix.diagonal_apply, hab]
  · simp [Pi.single_eq_of_ne h]

/-- Equality of the ground-field dimensions of every central component determines a module over
the full product of matrix blocks. -/
theorem nonempty_linearEquiv_of_component_finrank_eq
    (h : ∀ i,
      Module.finrank k
          (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) =
        Module.finrank k
          (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i)) :
    Nonempty (M ≃ₗ[AlgebraPi D d] N) := by
  letI componentBlockModuleM (i : ι) :
      Module (Block D d i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
    PiBlocks.componentModule (fun i ↦ Block D d i) i
  letI componentBlockModuleN (i : ι) :
      Module (Block D d i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i) :=
    PiBlocks.componentModule (fun i ↦ Block D d i) i
  letI componentDivisionModuleM (i : ι) :
      Module (D i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
    Module.compHom _ (Matrix.scalar (Fin (d i)))
  letI componentDivisionModuleN (i : ι) :
      Module (D i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i) :=
    Module.compHom _ (Matrix.scalar (Fin (d i)))
  letI componentDivisionTowerM (i : ι) :
      IsScalarTower (D i) (Block D d i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
    ⟨fun r s x ↦ by
      apply Subtype.ext
      change (Pi.single i (r • s) : AlgebraPi D d) • x.1 =
        (Pi.single i (Matrix.scalar (Fin (d i)) r) : AlgebraPi D d) •
          ((Pi.single i s : AlgebraPi D d) • x.1)
      rw [← mul_smul]
      congr 1
      ext j
      by_cases hij : j = i
      · subst j
        simp only [Pi.single_eq_same, Pi.mul_apply]
        have hrs : r • s = Matrix.scalar (Fin (d i)) r * s := by
          rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
        exact congrFun (congrFun hrs _ ) _
      · simp [Pi.single_eq_of_ne hij]⟩
  letI componentDivisionTowerN (i : ι) :
      IsScalarTower (D i) (Block D d i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i) :=
    ⟨fun r s x ↦ by
      apply Subtype.ext
      change (Pi.single i (r • s) : AlgebraPi D d) • x.1 =
        (Pi.single i (Matrix.scalar (Fin (d i)) r) : AlgebraPi D d) •
          ((Pi.single i s : AlgebraPi D d) • x.1)
      rw [← mul_smul]
      congr 1
      ext j
      by_cases hij : j = i
      · subst j
        simp only [Pi.single_eq_same, Pi.mul_apply]
        have hrs : r • s = Matrix.scalar (Fin (d i)) r * s := by
          rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
        exact congrFun (congrFun hrs _ ) _
      · simp [Pi.single_eq_of_ne hij]⟩
  letI componentGroundTowerM (i : ι) :
      IsScalarTower k (D i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
    ⟨component_smul_assoc k D d i⟩
  letI componentGroundTowerN (i : ι) :
      IsScalarTower k (D i)
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i) :=
    ⟨component_smul_assoc k D d i⟩
  letI componentGroundFiniteM (i : ι) :
      Module.Finite k
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i) :=
    Module.Finite.of_injective
      ((Submodule.subtype
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i)).restrictScalars k)
      Subtype.val_injective
  letI componentGroundFiniteN (i : ι) :
      Module.Finite k
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i) :=
    Module.Finite.of_injective
      ((Submodule.subtype
        (PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i)).restrictScalars k)
      Subtype.val_injective
  let e (i : ι) :
      PiBlocks.Component (R := fun i ↦ Block D d i) (M := M) i ≃ₗ[Block D d i]
        PiBlocks.Component (R := fun i ↦ Block D d i) (M := N) i :=
    (MatrixBlocks.nonempty_linearEquiv_of_restrictScalars_finrank_eq
      (D i) (Fin (d i)) _ _ (0 : Fin (d i)) (h i)).some
  exact ⟨(PiBlocks.decompose (fun i ↦ Block D d i)).trans
    ((PiBlocks.componentwiseLinearEquiv (fun i ↦ Block D d i) e).trans
      (PiBlocks.decompose (fun i ↦ Block D d i)).symm)⟩

end PiMatrixBlocks

namespace SemisimpleAlgebra

universe uK uA uM uN

variable {k : Type uK} {A : Type uA} {M : Type uM} {N : Type uN}
variable [Field k] [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A]
variable [AddCommGroup M] [Module k M] [Module.Finite k M]
variable [AddCommGroup N] [Module k N] [Module.Finite k N]
variable [Module A M] [Module A N]
variable [IsScalarTower k A M] [IsScalarTower k A N]

/-- Finite-dimensional modules over a semisimple algebra are determined by the characteristic
polynomials of every algebra element. The proof stays over the original, possibly imperfect,
ground field by using the division-algebra form of Wedderburn--Artin. -/
theorem nonempty_linearEquiv_of_charpoly_eq
    (hchar : ∀ a : A,
      (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly) :
    Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, D, d, hD, hAlg, hFinite, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k A
  letI : ∀ i, DivisionRing (D i) := hD
  letI : ∀ i, Algebra k (D i) := hAlg
  letI : ∀ i, Module.Finite k (D i) := hFinite
  letI : ∀ i, NeZero (d i) := hd
  let B := PiMatrixBlocks.AlgebraPi D d
  letI transportedModuleM : Module B M := Module.compHom M eA.symm.toRingHom
  letI transportedModuleN : Module B N := Module.compHom N eA.symm.toRingHom
  letI transportedTowerM : IsScalarTower k B M :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change eA.symm (algebraMap k B r) • x = r • x
      rw [eA.symm.commutes, IsScalarTower.algebraMap_smul]
  letI transportedTowerN : IsScalarTower k B N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change eA.symm (algebraMap k B r) • x = r • x
      rw [eA.symm.commutes, IsScalarTower.algebraMap_smul]
  have hcomponents : ∀ i,
      Module.finrank k
          (PiBlocks.Component (R := fun i ↦ PiMatrixBlocks.Block D d i) (M := M) i) =
        Module.finrank k
          (PiBlocks.Component (R := fun i ↦ PiMatrixBlocks.Block D d i) (M := N) i) := by
    intro i
    let c : B :=
      PiBlocks.coordinateIdempotent (fun i ↦ PiMatrixBlocks.Block D d i) i
    have hc : IsIdempotentElem c :=
      PiBlocks.coordinateIdempotent_idem (fun i ↦ PiMatrixBlocks.Block D d i) i
    have hcharB :
        (Algebra.lsmul k k M c).charpoly = (Algebra.lsmul k k N c).charpoly := by
      change (Algebra.lsmul k k M (eA.symm c)).charpoly =
        (Algebra.lsmul k k N (eA.symm c)).charpoly
      exact hchar (eA.symm c)
    calc
      Module.finrank k
          (PiBlocks.Component (R := fun i ↦ PiMatrixBlocks.Block D d i) (M := M) i) =
          Module.finrank k (LinearMap.range (Algebra.lsmul k k M c)) :=
        PiBlocks.finrank_component_eq_range_lsmul
          (M := M) (fun i ↦ PiMatrixBlocks.Block D d i) i
      _ = Module.finrank k (LinearMap.range (Algebra.lsmul k k N c)) :=
        finrank_range_lsmul_eq_of_charpoly_eq_of_isIdempotentElem c hc hcharB
      _ = Module.finrank k
          (PiBlocks.Component (R := fun i ↦ PiMatrixBlocks.Block D d i) (M := N) i) :=
        (PiBlocks.finrank_component_eq_range_lsmul
          (M := N) (fun i ↦ PiMatrixBlocks.Block D d i) i).symm
  obtain ⟨eB⟩ := PiMatrixBlocks.nonempty_linearEquiv_of_component_finrank_eq
    k D d hcomponents
  refine ⟨{
    toFun := eB
    invFun := eB.symm
    left_inv := eB.left_inv
    right_inv := eB.right_inv
    map_add' := eB.map_add
    map_smul' := ?_ }⟩
  intro a x
  simp only [RingHom.id_apply]
  have h := eB.map_smul (eA a) x
  change eB (eA.symm (eA a) • x) = eA.symm (eA a) • eB x at h
  simpa using h

end SemisimpleAlgebra

end FLT.Components.BrauerNesbitt

end
