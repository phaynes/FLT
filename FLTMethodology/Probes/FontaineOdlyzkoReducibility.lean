import FLT.Slop.RepresentationTheory.OddAbsIrredSlop
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Reducibility bridge leaf for the proposed Fontaine--Odlyzko route.

This module isolates the *pure linear-algebraic* consequence of reducibility for a rank-two Galois
representation: a non-irreducible rank-two representation possesses a proper stable line, its
quotient is one-dimensional, and the canonical quotient map is a surjective equivariant intertwiner
onto the induced quotient representation.

This is **only** the reducibility node. It deliberately does *not* assert that the quotient action
is trivial, does not choose a quotient coordinate, does not build any scalar functional or quotient
character, and makes no use of hardly-ramified local/global input. The first residual mathematical
goal — using that input to select and orient a stable line whose quotient character is trivial —
is left open. Consequently this module cannot promote `FLT-FONTAINE-ODLYZKO`.
-/

namespace FLTProbe.FontaineOdlyzko

universe uK uV

variable {k : Type uK} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- Pure linear-algebraic output of reducibility for a rank-two Galois representation.
It deliberately does not assert that the quotient action is trivial. -/
structure ReducibleRankTwoData
    [TopologicalSpace k] (rho : GaloisRep ℚ k V) where
  W : Subrepresentation rho.toRepresentation
  W_ne_bot : W ≠ ⊥
  W_ne_top : W ≠ ⊤
  finrank_W : Module.finrank k W.toSubmodule = 1
  finrank_quotient : Module.finrank k (V ⧸ W.toSubmodule) = 1

/-- A non-irreducible rank-two representation has a proper stable line and a
one-dimensional quotient. -/
theorem exists_reducibleRankTwoData
    [TopologicalSpace k] [Module.Finite k V] [Module.Free k V]
    (rho : GaloisRep ℚ k V) (hV : Module.rank k V = 2)
    (hred : ¬ rho.IsIrreducible) :
    Nonempty (ReducibleRankTwoData rho) := by
  have hfinV : Module.finrank k V = 2 := by
    rw [← Module.finrank_eq_rank] at hV
    exact_mod_cast hV
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (n := 1) hfinV
  have hnotAll : ¬ ∀ W : Submodule k V,
      (∀ g : Field.absoluteGaloisGroup ℚ, ∀ v ∈ W,
        rho.toRepresentation g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro hAll
    apply hred
    exact (Slop.OddRep.isIrreducible_iff_forall rho.toRepresentation).2
      ⟨inferInstance, hAll⟩
  push Not at hnotAll
  obtain ⟨W, hstable, hWbot, hWtop⟩ := hnotAll
  let Wrep : Subrepresentation rho.toRepresentation := ⟨W, hstable⟩
  have hWrepBot : Wrep ≠ ⊥ := by
    intro h
    exact hWbot (congrArg Subrepresentation.toSubmodule h)
  have hWrepTop : Wrep ≠ ⊤ := by
    intro h
    exact hWtop (congrArg Subrepresentation.toSubmodule h)
  have hWlt : Module.finrank k W < 2 := by
    simpa [hfinV] using Submodule.finrank_lt hWtop
  have hWne : Module.finrank k W ≠ 0 := by
    intro hzero
    exact hWbot (Submodule.finrank_eq_zero.mp hzero)
  have hWfin : Module.finrank k W = 1 := by omega
  have hquot := W.finrank_quotient_add_finrank
  have hQfin : Module.finrank k (V ⧸ W) = 1 := by omega
  exact ⟨⟨Wrep, hWrepBot, hWrepTop, hWfin, hQfin⟩⟩

/-- The canonical quotient representation carried by the stable line. -/
noncomputable def ReducibleRankTwoData.quotientRepresentation
    [TopologicalSpace k] {rho : GaloisRep ℚ k V}
    (D : ReducibleRankTwoData rho) :
    Representation k (Field.absoluteGaloisGroup ℚ) (V ⧸ D.W.toSubmodule) :=
  rho.toRepresentation.quotient D.W.toSubmodule fun g _ hv =>
    D.W.apply_mem_toSubmodule g hv

/-- The canonical quotient map is surjective. -/
theorem ReducibleRankTwoData.quotient_surjective
    [TopologicalSpace k] {rho : GaloisRep ℚ k V}
    (D : ReducibleRankTwoData rho) :
    Function.Surjective D.W.toSubmodule.mkQ :=
  D.W.toSubmodule.mkQ_surjective

/-- The canonical quotient map intertwines the original and quotient actions. -/
theorem ReducibleRankTwoData.quotient_equivariant
    [TopologicalSpace k] {rho : GaloisRep ℚ k V}
    (D : ReducibleRankTwoData rho)
    (g : Field.absoluteGaloisGroup ℚ) (v : V) :
    D.W.toSubmodule.mkQ (rho g v) =
      D.quotientRepresentation g (D.W.toSubmodule.mkQ v) := by
  rfl

#check ReducibleRankTwoData
#check exists_reducibleRankTwoData
#check ReducibleRankTwoData.quotientRepresentation
#check ReducibleRankTwoData.quotient_surjective
#check ReducibleRankTwoData.quotient_equivariant

#print axioms ReducibleRankTwoData
#print axioms exists_reducibleRankTwoData
#print axioms ReducibleRankTwoData.quotientRepresentation
#print axioms ReducibleRankTwoData.quotient_surjective
#print axioms ReducibleRankTwoData.quotient_equivariant

end FLTProbe.FontaineOdlyzko
