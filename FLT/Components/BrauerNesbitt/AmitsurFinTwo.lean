/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.IdempotentCharpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The degree-two Amitsur identity

This file proves the denominator-free degree-two case of Amitsur's formula.  It is valid in every
characteristic.  Consequently, characteristic-polynomial equality on a spanning family extends to
the whole algebra for two-dimensional representations, provided the two algebra actions are
multiplicative.
-/

@[expose] public section

namespace FLT.Components.BrauerNesbitt

open Polynomial

universe uK uA uM uN

variable {k : Type uK} [Field k]

/-- The degree-two determinant-of-a-sum identity.  This is Amitsur's formula in degree two. -/
theorem Matrix.det_add_fin_two (A B : Matrix (Fin 2) (Fin 2) k) :
    (A + B).det = A.det + B.det + A.trace * B.trace - (A * B).trace := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

/-- The degree-two determinant-of-a-sum identity for endomorphisms. -/
theorem LinearMap.det_add_of_finrank_eq_two
    {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hM : Module.finrank k M = 2) (f g : Module.End k M) :
    LinearMap.det (f + g) = LinearMap.det f + LinearMap.det g +
      LinearMap.trace k M f * LinearMap.trace k M g - LinearMap.trace k M (f * g) := by
  let b := Module.finBasisOfFinrankEq k M hM
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b,
    LinearMap.trace_eq_matrix_trace k b, LinearMap.trace_eq_matrix_trace k b,
    LinearMap.trace_eq_matrix_trace k b]
  simpa only [(LinearMap.toMatrix b b).map_add, LinearMap.toMatrix_mul] using
    Matrix.det_add_fin_two (LinearMap.toMatrix b b f) (LinearMap.toMatrix b b g)

/-- In dimension two the characteristic polynomial is determined by trace and determinant. -/
theorem LinearMap.charpoly_of_finrank_eq_two
    {M : Type uM} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hM : Module.finrank k M = 2) (f : Module.End k M) :
    f.charpoly = X ^ 2 - C (LinearMap.trace k M f) * X + C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq k M hM
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace k b, ← LinearMap.det_toMatrix b f]

/-- Degree-two characteristic-polynomial equality extends from a spanning family to the entire
algebra.  Unlike polynomial interpolation, this is valid over finite fields and in characteristic
two: the proof uses the denominator-free Amitsur identity and multiplicativity of the actions. -/
theorem charpoly_eq_of_finrank_eq_two_of_span
    {A : Type uA} [Ring A] [Algebra k A]
    {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    [AddCommGroup N] [Module k N] [Module.Finite k N]
    (hM : Module.finrank k M = 2) (hN : Module.finrank k N = 2)
    (phi : A →ₐ[k] Module.End k M) (psi : A →ₐ[k] Module.End k N)
    (S : Set A) (hspan : Submodule.span k S = ⊤)
    (hchar : ∀ s ∈ S, (phi s).charpoly = (psi s).charpoly) :
    ∀ a : A, (phi a).charpoly = (psi a).charpoly := by
  have htrace : ∀ a : A,
      LinearMap.trace k M (phi a) = LinearMap.trace k N (psi a) := by
    intro a
    have ha : a ∈ Submodule.span k S := by rw [hspan]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun a _ ↦ LinearMap.trace k M (phi a) = LinearMap.trace k N (psi a))
      ?_ ?_ ?_ ?_ ha
    · intro s hs
      exact trace_eq_of_charpoly_eq (phi s) (psi s) (hchar s hs)
    · simp
    · intro x y _ _ hx hy
      simpa using congrArg₂ (· + ·) hx hy
    · intro c x _ hx
      simpa using congrArg (c * ·) hx
  have hdet : ∀ a : A, LinearMap.det (phi a) = LinearMap.det (psi a) := by
    intro a
    have ha : a ∈ Submodule.span k S := by rw [hspan]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun a _ ↦ LinearMap.det (phi a) = LinearMap.det (psi a))
      ?_ ?_ ?_ ?_ ha
    · intro s hs
      have hp := hchar s hs
      rw [LinearMap.charpoly_of_finrank_eq_two hM,
        LinearMap.charpoly_of_finrank_eq_two hN] at hp
      have hc := congrArg (fun p : k[X] ↦ p.coeff 0) hp
      simpa using hc
    · simp [hM, hN]
    · intro x y _ _ hx hy
      rw [show phi (x + y) = phi x + phi y by exact map_add phi.toLinearMap x y,
        show psi (x + y) = psi x + psi y by exact map_add psi.toLinearMap x y,
        LinearMap.det_add_of_finrank_eq_two hM,
        LinearMap.det_add_of_finrank_eq_two hN, hx, hy, htrace x, htrace y]
      have hxy := htrace (x * y)
      simp only [map_mul] at hxy
      rw [hxy]
    · intro c x _ hx
      rw [show phi (c • x) = c • phi x by exact map_smul phi.toLinearMap c x,
        show psi (c • x) = c • psi x by exact map_smul psi.toLinearMap c x,
        LinearMap.det_smul, LinearMap.det_smul, hM, hN, hx]
  intro a
  rw [LinearMap.charpoly_of_finrank_eq_two hM,
    LinearMap.charpoly_of_finrank_eq_two hN, htrace a, hdet a]

open Representation

universe uG uV uW

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W]

omit [Module.Finite k V] [Module.Finite k W] in
/-- The actual group elements span the joint-image algebra, now stated internally in that
algebra rather than in the ambient product of endomorphism rings. -/
theorem span_range_jointImageElement
    (rho : Representation k G V) (sigma : Representation k G W) :
    Submodule.span k (Set.range (jointImageElement rho sigma)) = ⊤ := by
  apply top_unique
  rintro a -
  have ha : a.1 ∈ jointImageSpan rho sigma := a.2
  refine Submodule.span_induction
    (p := fun x hx ↦ (⟨x, hx⟩ : jointImageAlgebra rho sigma) ∈
      Submodule.span k (Set.range (jointImageElement rho sigma)))
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨g, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self g)
  · convert (Submodule.span k (Set.range (jointImageElement rho sigma))).zero_mem using 1
    apply Subtype.ext
    rfl
  · intro x y hx hy hxm hym
    convert (Submodule.span k (Set.range (jointImageElement rho sigma))).add_mem hxm hym using 1
    apply Subtype.ext
    rfl
  · intro c x hx hxm
    convert (Submodule.span k (Set.range (jointImageElement rho sigma))).smul_mem c hxm using 1
    apply Subtype.ext
    rfl

/-- For two-dimensional representations, equality on all group elements extends to equality on
the complete joint-image algebra.  This is the exact degree-two Amitsur bridge needed before
idempotent multiplicities can be compared. -/
theorem charpoly_jointImage_eq_of_finrank_eq_two
    (rho : Representation k G V) (sigma : Representation k G W)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (hchar : ∀ g, (rho g).charpoly = (sigma g).charpoly) :
    ∀ a : jointImageAlgebra rho sigma,
      (jointImageFst rho sigma a).charpoly = (jointImageSnd rho sigma a).charpoly := by
  apply charpoly_eq_of_finrank_eq_two_of_span hV hW
    (jointImageFst rho sigma) (jointImageSnd rho sigma)
    (Set.range (jointImageElement rho sigma))
    (span_range_jointImageElement rho sigma)
  rintro _ ⟨g, rfl⟩
  simpa using hchar g

end FLT.Components.BrauerNesbitt

end
