/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.Contracts.BrauerNesbitt
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Brauer--Nesbitt joint-image algebra

This module proves the structural tranche needed before the arbitrary-field Brauer--Nesbitt
multiplicity argument: the group algebra surjects onto the joint-image algebra, semisimplicity of
each representation descends to its joint-image module, and the joint-image algebra is semisimple.
-/

@[expose] public section

open scoped MonoidAlgebra

namespace FLT.Components.BrauerNesbitt

open Representation

universe uK uG uV uW

variable {k : Type uK} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable (rho : Representation k G V) (sigma : Representation k G W)

/-- The group homomorphism from `G` into the joint-image algebra. -/
noncomputable def jointImageMonoidHom : G →* jointImageAlgebra rho sigma where
  toFun := jointImageElement rho sigma
  map_one' := Subtype.ext (by simp [jointImageElement, jointImagePoint])
  map_mul' g h := Subtype.ext (by simp [jointImageElement, jointImagePoint])

/-- The group-algebra action corestricted to the joint-image algebra. -/
noncomputable def jointImageAlgHom : k[G] →ₐ[k] jointImageAlgebra rho sigma :=
  MonoidAlgebra.lift k (jointImageAlgebra rho sigma) G (jointImageMonoidHom rho sigma)

@[simp]
theorem jointImageAlgHom_of (g : G) :
    jointImageAlgHom rho sigma (MonoidAlgebra.of k G g) = jointImageElement rho sigma g := by
  simp [jointImageAlgHom, jointImageMonoidHom]

/-- The group algebra spans, and therefore surjects onto, the joint-image algebra. -/
theorem jointImageAlgHom_surjective : Function.Surjective (jointImageAlgHom rho sigma) := by
  rintro ⟨a, ha⟩
  change a ∈ jointImageSpan rho sigma at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro x ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of k G g, jointImageAlgHom_of rho sigma g⟩
  · exact ⟨0, Subtype.ext (by simp)⟩
  · rintro x y hx hy ⟨px, hpx⟩ ⟨py, hpy⟩
    refine ⟨px + py, Subtype.ext ?_⟩
    simpa using congrArg₂ (· + ·) (congrArg Subtype.val hpx) (congrArg Subtype.val hpy)
  · rintro c x hx ⟨px, hpx⟩
    refine ⟨c • px, Subtype.ext ?_⟩
    simpa using congrArg (c • ·) (congrArg Subtype.val hpx)

theorem jointImageFst_comp_jointImageAlgHom :
    (jointImageFst rho sigma).comp (jointImageAlgHom rho sigma) = rho.asAlgebraHom := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    change jointImageFst rho sigma (jointImageAlgHom rho sigma (MonoidAlgebra.of k G g)) =
      rho.asAlgebraHom (MonoidAlgebra.of k G g)
    rw [jointImageAlgHom_of, jointImageFst_element, Representation.asAlgebraHom_of]
  · ext

theorem jointImageSnd_comp_jointImageAlgHom :
    (jointImageSnd rho sigma).comp (jointImageAlgHom rho sigma) = sigma.asAlgebraHom := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    change jointImageSnd rho sigma (jointImageAlgHom rho sigma (MonoidAlgebra.of k G g)) =
      sigma.asAlgebraHom (MonoidAlgebra.of k G g)
    rw [jointImageAlgHom_of, jointImageSnd_element, Representation.asAlgebraHom_of]
  · ext

/-- `V` as a module over the joint-image algebra via its first projection. -/
@[reducible]
noncomputable def fstModule : Module (jointImageAlgebra rho sigma) V :=
  Module.compHom V (jointImageFst rho sigma).toRingHom

/-- `W` as a module over the joint-image algebra via its second projection. -/
@[reducible]
noncomputable def sndModule : Module (jointImageAlgebra rho sigma) W :=
  Module.compHom W (jointImageSnd rho sigma).toRingHom

/-- Semisimplicity of `rho` descends through the surjective joint-image action. -/
theorem isSemisimpleModule_fst
    (hrho : Representation.IsSemisimpleRepresentation rho) :
    letI := fstModule rho sigma
    IsSemisimpleModule (jointImageAlgebra rho sigma) V := by
  letI := fstModule rho sigma
  letI : RingHomSurjective (jointImageAlgHom rho sigma).toRingHom :=
    ⟨jointImageAlgHom_surjective rho sigma⟩
  let f : rho.asModule →ₛₗ[(jointImageAlgHom rho sigma).toRingHom] V :=
    { AddMonoidHom.id V with
      map_smul' := fun c x ↦ by
        change rho.asAlgebraHom c x =
          jointImageFst rho sigma (jointImageAlgHom rho sigma c) x
        rw [← AlgHom.congr_fun (jointImageFst_comp_jointImageAlgHom rho sigma) c]
        rfl }
  apply (f.isSemisimpleModule_iff_of_bijective Function.bijective_id).mp
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp hrho

/-- Semisimplicity of `sigma` descends through the surjective joint-image action. -/
theorem isSemisimpleModule_snd
    (hsigma : Representation.IsSemisimpleRepresentation sigma) :
    letI := sndModule rho sigma
    IsSemisimpleModule (jointImageAlgebra rho sigma) W := by
  letI := sndModule rho sigma
  letI : RingHomSurjective (jointImageAlgHom rho sigma).toRingHom :=
    ⟨jointImageAlgHom_surjective rho sigma⟩
  let f : sigma.asModule →ₛₗ[(jointImageAlgHom rho sigma).toRingHom] W :=
    { AddMonoidHom.id W with
      map_smul' := fun c x ↦ by
        change sigma.asAlgebraHom c x =
          jointImageSnd rho sigma (jointImageAlgHom rho sigma c) x
        rw [← AlgHom.congr_fun (jointImageSnd_comp_jointImageAlgHom rho sigma) c]
        rfl }
  apply (f.isSemisimpleModule_iff_of_bijective Function.bijective_id).mp
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule sigma).mp hsigma

/-- The paired action is faithful because a joint-image element is exactly its two projections. -/
theorem faithfulSMul_prod :
    letI := fstModule rho sigma
    letI := sndModule rho sigma
    FaithfulSMul (jointImageAlgebra rho sigma) (V × W) := by
  letI := fstModule rho sigma
  letI := sndModule rho sigma
  constructor
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    have hv := congrArg Prod.fst (h (v, 0))
    exact hv
  · apply LinearMap.ext
    intro w
    have hw := congrArg Prod.snd (h (0, w))
    exact hw

/-- A linear equivalence over the joint-image algebra is automatically an equivalence of the
original group representations. -/
noncomputable def representationEquivOfJointImageLinearEquiv
    (rho : Representation k G V) (sigma : Representation k G W) :
    letI := fstModule rho sigma
    letI := sndModule rho sigma
    (V ≃ₗ[jointImageAlgebra rho sigma] W) → Representation.Equiv rho sigma := by
  letI := fstModule rho sigma
  letI := sndModule rho sigma
  letI : IsScalarTower k (jointImageAlgebra rho sigma) V :=
    IsScalarTower.of_compHom k (jointImageAlgebra rho sigma) V
  letI : IsScalarTower k (jointImageAlgebra rho sigma) W :=
    IsScalarTower.of_compHom k (jointImageAlgebra rho sigma) W
  intro e
  apply Representation.Equiv.mk (e.restrictScalars k)
  intro g
  apply LinearMap.ext
  intro v
  change e (rho g v) = sigma g (e v)
  have h := e.map_smul (jointImageElement rho sigma g) v
  change e (jointImageFst rho sigma (jointImageElement rho sigma g) v) =
    jointImageSnd rho sigma (jointImageElement rho sigma g) (e v) at h
  simpa only [jointImageFst_element, jointImageSnd_element] using h

/-- Nonempty joint-image linear equivalence is enough for the representation-level conclusion. -/
theorem nonempty_representationEquiv_of_jointImageLinearEquiv
    (rho : Representation k G V) (sigma : Representation k G W) :
    letI := fstModule rho sigma
    letI := sndModule rho sigma
    Nonempty (V ≃ₗ[jointImageAlgebra rho sigma] W) →
      Nonempty (Representation.Equiv rho sigma) := by
  letI := fstModule rho sigma
  letI := sndModule rho sigma
  exact Nonempty.map (representationEquivOfJointImageLinearEquiv rho sigma)

variable [Module.Finite k V] [Module.Finite k W]

/-- The joint-image algebra of two semisimple finite-dimensional representations is semisimple. -/
theorem isSemisimpleRing_jointImageAlgebra
    (hrho : Representation.IsSemisimpleRepresentation rho)
    (hsigma : Representation.IsSemisimpleRepresentation sigma) :
    IsSemisimpleRing (jointImageAlgebra rho sigma) := by
  letI := fstModule rho sigma
  letI := sndModule rho sigma
  letI : IsSemisimpleModule (jointImageAlgebra rho sigma) V :=
    isSemisimpleModule_fst rho sigma hrho
  letI : IsSemisimpleModule (jointImageAlgebra rho sigma) W :=
    isSemisimpleModule_snd rho sigma hsigma
  letI : Module.Finite k (jointImageAlgebra rho sigma) :=
    FiniteDimensional.of_injective (jointImageAlgebra rho sigma).val.toLinearMap
      Subtype.val_injective
  letI : IsArtinianRing (jointImageAlgebra rho sigma) :=
    IsArtinianRing.of_finite k (jointImageAlgebra rho sigma)
  apply IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
  apply le_bot_iff.mp
  calc
    Ring.jacobson (jointImageAlgebra rho sigma) ≤
        Module.annihilator (jointImageAlgebra rho sigma) V ⊓
          Module.annihilator (jointImageAlgebra rho sigma) W :=
      le_inf
        (IsSemisimpleModule.jacobson_le_annihilator (jointImageAlgebra rho sigma) V)
        (IsSemisimpleModule.jacobson_le_annihilator (jointImageAlgebra rho sigma) W)
    _ = Module.annihilator (jointImageAlgebra rho sigma) (V × W) :=
      (Module.annihilator_prod).symm
    _ = ⊥ := Module.annihilator_eq_bot.mpr (faithfulSMul_prod rho sigma)

end FLT.Components.BrauerNesbitt

end
