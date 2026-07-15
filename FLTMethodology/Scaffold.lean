/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT

public section

/-!
# FLT methodology scaffold

This module is outside the `FLT` library root and is not imported by the public theorem. Every
admission is an architecture marker, not proof progress. Obligation IDs link admissions to the
machine-readable graph.

The scaffold intentionally stops at `FLT-SGOOD-DEF`: the frozen blueprint does not identify an
exact modularity-lifting source whose hypotheses match its intended theorem. Inventing a weaker
proposition would make the design look more complete while losing the mathematical contract.
-/

namespace FLTMethodology

open GaloisRepresentation

universe u v

/-- `FLT-HR-REDUCIBLE`: exact generic B5-shaped contract over the upstream coefficient interface. -/
def HardlyRamifiedReducibilityContract : Prop :=
  ∀ (ell : ℕ) (hEllOdd : Odd ell) (_ : Fact ell.Prime)
    (k : Type u) (_ : Finite k) (_ : Field k)
    (_ : TopologicalSpace k) (_ : DiscreteTopology k)
    (_ : Algebra ℤ_[ell] k) (_ : IsLocalHom (algebraMap ℤ_[ell] k))
    (V : Type v) (_ : AddCommGroup V) (_ : Module k V)
    (_ : Module.Finite k V) (_ : Module.Free k V)
    (hV : Module.rank k V = 2)
    (rho : GaloisRep ℚ k V),
    IsHardlyRamified hEllOdd hV rho → ¬ rho.IsIrreducible

/-- Admission `FLT-HR-REDUCIBLE`; elaboration of the intended generic endpoint only. -/
theorem hardlyRamifiedReducibility_scaffold : HardlyRamifiedReducibilityContract := by
  sorry

/-- `FLT-B4`: the frozen public B4 endpoint, kept separate from the generic B5 contract. -/
theorem b4_scaffold : FLT.Bosses.B4 := by
  sorry

/-- `FLT-B1`: the frozen Mathlib-form endpoint. -/
theorem flt_scaffold : FermatLastTheorem := by
  sorry

/-- `FLT-TOP`: the frozen positive-natural endpoint. -/
theorem positiveNaturals_scaffold
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n := by
  sorry

/--
`FLT-MLT-SOURCE` and `FLT-SGOOD-DEF`: a non-empty record of the exact unresolved source
conditions. This is metadata, not a mathematical substitute for the absent definition.
-/
structure ModularityLiftingSourceGap where
  sourceLocator : String
  residualImageCondition : String
  ellBehaviourInBaseField : String
  localDeformationCondition : String
  mismatchIsResolved : Bool

/-- The frozen design has not resolved the modularity-lifting source mismatch. -/
def frozenModularityLiftingGap : ModularityLiftingSourceGap where
  sourceLocator := "blueprint chapter 4; exact primary theorem not selected"
  residualImageCondition := "candidate sources impose different residual-image hypotheses"
  ellBehaviourInBaseField := "unramified in the blueprint versus split in one near-reference"
  localDeformationCondition := "the temporary S-good condition lacks a frozen Lean definition"
  mismatchIsResolved := false

end FLTMethodology

end
