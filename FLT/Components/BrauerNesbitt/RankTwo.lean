/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Components.BrauerNesbitt.SemisimpleReconstruction

/-!
# Rank-two Brauer--Nesbitt over an arbitrary field

This module combines the degree-two Amitsur extension with semisimple-algebra reconstruction over
division-algebra Wedderburn blocks. It does not pass to a splitting field, so no perfectness or
algebraic-closure hypothesis is required.
-/

@[expose] public section

namespace FLT.Components.BrauerNesbitt

open Representation

universe uK uG uV uW

variable {k : Type uK} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- Two-dimensional semisimple representations over an arbitrary field are equivalent when their
characteristic polynomials agree on every group element. -/
theorem nonempty_representationEquiv_of_finrank_eq_two
    (rho : Representation k G V) (sigma : Representation k G W)
    (hrho : Representation.IsSemisimpleRepresentation rho)
    (hsigma : Representation.IsSemisimpleRepresentation sigma)
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (hchar : ∀ g, (rho g).charpoly = (sigma g).charpoly) :
    Nonempty (Representation.Equiv rho sigma) := by
  let A := jointImageAlgebra rho sigma
  letI : Module A V := fstModule rho sigma
  letI : Module A W := sndModule rho sigma
  letI : IsScalarTower k A V := IsScalarTower.of_compHom k A V
  letI : IsScalarTower k A W := IsScalarTower.of_compHom k A W
  letI : Module.Finite k A :=
    FiniteDimensional.of_injective A.val.toLinearMap Subtype.val_injective
  letI : IsSemisimpleRing A := isSemisimpleRing_jointImageAlgebra rho sigma hrho hsigma
  have hcharA : ∀ a : A,
      (Algebra.lsmul k k V a).charpoly = (Algebra.lsmul k k W a).charpoly := by
    intro a
    change (jointImageFst rho sigma a).charpoly = (jointImageSnd rho sigma a).charpoly
    exact charpoly_jointImage_eq_of_finrank_eq_two rho sigma hV hW hchar a
  obtain ⟨e⟩ := SemisimpleAlgebra.nonempty_linearEquiv_of_charpoly_eq hcharA
  exact nonempty_representationEquiv_of_jointImageLinearEquiv rho sigma ⟨e⟩

/-- The exact rank-two group-representation contract used by the FLT residual and characteristic
zero coefficient branches. -/
def RankTwoContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
      Representation.IsSemisimpleRepresentation sigma →
      Module.finrank k V = 2 →
      Module.finrank k W = 2 →
      (∀ g, (rho g).charpoly = (sigma g).charpoly) →
      Nonempty (Representation.Equiv rho sigma)

/-- Kernel-clean witness for the rank-two Brauer--Nesbitt contract. -/
theorem rankTwoContract : RankTwoContract := by
  intro k G V W _ _ _ _ _ _ _ _ rho sigma hrho hsigma hV hW hchar
  exact nonempty_representationEquiv_of_finrank_eq_two
    rho sigma hrho hsigma hV hW hchar

end FLT.Components.BrauerNesbitt

end
