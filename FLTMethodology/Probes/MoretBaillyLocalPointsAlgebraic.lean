import FLT

/-!
# Algebraic scheme-valued-point boundary for Moret--Bailly

This methodology-only file records the algebraic point type and its functoriality under extension
of the coefficient algebra. It deliberately supplies no topology on local points, no local-open
comparison theorem, and no Moret--Bailly existence theorem.
-/

namespace FLT.PotentialModularity.MoretBailly

open AlgebraicGeometry CategoryTheory

universe u

/-- Field-valued points of a scheme over the selected base field. -/
def _root_.AlgebraicGeometry.Scheme.ptsOver
    (X : Scheme.{u}) (K : Type u) [Field K]
    [X.Over (Spec (CommRingCat.of K))]
    (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  { f : Spec (CommRingCat.of R) ⟶ X //
      f ≫ (X ↘ Spec (CommRingCat.of K)) =
        Spec.map (CommRingCat.ofHom (algebraMap K R)) }

/-- Functoriality of field-valued points along a base-algebra homomorphism. -/
noncomputable def ptsMap
    {X : Scheme.{u}} {K : Type u} [Field K]
    [X.Over (Spec (CommRingCat.of K))]
    {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) : X.ptsOver K R → X.ptsOver K S :=
  fun f ↦ ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f.1, by
    rw [Category.assoc, f.2]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact φ.commutes x⟩

#check AlgebraicGeometry.Scheme.ptsOver
#check ptsMap
#print axioms AlgebraicGeometry.Scheme.ptsOver
#print axioms ptsMap

end FLT.PotentialModularity.MoretBailly
