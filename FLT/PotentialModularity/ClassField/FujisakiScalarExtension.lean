/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.DivisionAlgebra.Finiteness

/-!
# Fujisaki scalar-extension comparison

The Fujisaki quotient in `Finiteness.lean` uses a scalar-extension presentation even when its
division algebra is specialized to the base field. This file supplies the Lean-internal continuous
algebra equivalence between that presentation and the repository's adele ring.

Voight presents the adele ring as a restricted direct product and uses scalar extension for the
division algebra; this declaration does not replace that source presentation.
-/

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- The scalar-extension presentation used by the Fujisaki theorem is continuously equivalent to
the repository's adele-ring presentation. -/
public noncomputable def adeleScalarExtensionContinuousAlgEquiv :
    (K ⊗[K] AdeleRing (𝓞 K) K) ≃A[K] AdeleRing (𝓞 K) K := by
  letI : Algebra (AdeleRing (𝓞 K) K) (K ⊗[K] AdeleRing (𝓞 K) K) :=
    TensorProduct.RightActions.instAlgebra_fLT K (AdeleRing (𝓞 K) K) K
  letI : SMul (AdeleRing (𝓞 K) K) (K ⊗[K] AdeleRing (𝓞 K) K) :=
    Algebra.toSMul
  letI : Module (AdeleRing (𝓞 K) K) (K ⊗[K] AdeleRing (𝓞 K) K) :=
    Algebra.toModule
  haveI : IsBiscalar K (AdeleRing (𝓞 K) K)
      ⇑(Algebra.TensorProduct.lid K (AdeleRing (𝓞 K) K)).toAlgHom :=
    { map_smul₁ := fun r a => map_smul _ r a
      map_smul₂ := by
        intro a x
        simp only [Algebra.smul_def]
        rw [map_mul]
        congr 1
        change (Algebra.TensorProduct.lid K (AdeleRing (𝓞 K) K))
            ((1 : K) ⊗ₜ[K] a) = a
        simp }
  exact IsModuleTopology.continuousAlgEquivOfIsBiscalar
    (AdeleRing (𝓞 K) K)
    (Algebra.TensorProduct.lid K (AdeleRing (𝓞 K) K))

end FLT.PotentialModularity.ClassField
