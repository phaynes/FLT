import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Deformations.RepresentationTheory.Irreducible
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
Neutral residual-closure absolute-irreducibility vocabulary for the Taylor-2018
modularity-lifting source boundary (`FLT-ABSIRRED-VOCAB`).

This file provides only definitions. It states two residual-closure absolute-irreducibility
predicates and one open provider contract. Absolute irreducibility is tested in the common residual
closure `AlgebraicClosure (ZMod ell)` via an explicit coefficient embedding, going through
`GaloisRep.toRepresentation` and `Representation.baseChange` (both topology-free).

`ClosureImpliesClassAbsIrred` names — but does NOT prove — the implication from the residual-closure
form to the repository `∀`-extension class `Representation.IsAbsolutelyIrreducible`. That implication
remains an open provider proposition (the first residual goal, discharged by Burnside/Schur over the
algebraically closed residual field), not a proved theorem.
-/

namespace FLTMethodology.Taylor2018

universe uK uk uW

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
This is NOT proved here; it names the open provider proposition. Owner `FLT-ABSIRRED-VOCAB`. -/
def ClosureImpliesClassAbsIrred
    {K : Type uK} [Field K] [NumberField K]
    (ell : ℕ) [Fact ell.Prime]
    {k : Type uk} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (f : k →+* AlgebraicClosure (ZMod ell))
    (ρbar : GaloisRep K k W) : Prop :=
  IsAbsolutelyIrreducibleInResidualClosure ell f ρbar →
    Representation.IsAbsolutelyIrreducible.{max uK uk uW, uK, uk, uW} ρbar.toRepresentation

end FLTMethodology.Taylor2018
