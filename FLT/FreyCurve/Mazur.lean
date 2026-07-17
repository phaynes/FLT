/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
import FLT.GaloisRepresentation.HardlyRamified.Frey
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!

# Irreducibility of the p-torsion of the Frey curve

A deep result of Mazur implies that the Frey curve is irreducible.

-/

@[expose] public section

open WeierstrassCurve

namespace Serre1987

/-- Serre 1987, §4.1, Proposition 6, printed p. 201. For a semistable Frey curve
with full rational two-torsion and prime `p ≥ 5`, Serre's two character cases and the odd-degree
quotient isogeny retain the full two-torsion needed for the Mazur torsion contradiction. This is a
named T2 historical boundary; its unconditional T3 proof remains separate. -/
axiom freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos)

end Serre1987

/--
The p-torsion in the Frey curve associated to a counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  exact Serre1987.freyCurve_galoisRep_isIrreducible P
