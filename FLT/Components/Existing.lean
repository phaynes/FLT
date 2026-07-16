/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Basic.Lemmas
public import FLT.FreyCurve.Basic
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.ModularityLifting.Conditions
public import FLT.GaloisRepresentation.Automorphic
public import FLT.Deformations.RepresentationTheory.GaloisRepFamily

/-!
# Existing kernel-clean FLT contracts

This module is the stable import surface for mathematical vocabulary and elementary adapters that
are already kernel-clean in the frozen repository. It deliberately does not import `FLT.Proof`, the
concrete Frey `galoisRep`, Mazur's theorem, or the hardly-ramified provider implementations.

Some source modules also contain admitted theorems. In particular, importing automorphy vocabulary
does not make `cyclic_base_change` proved. Consumers must use the separately owned provider
contract; the audit file records the contaminated declarations explicitly.
-/

@[expose] public section

namespace FLT.Components.Existing

/-- The clean B1 vocabulary, definitionally equal to the frozen repository B1. -/
abbrev BossB1 : Prop := FermatLastTheorem

/-- The clean B2 vocabulary, definitionally equal to the frozen repository B2. -/
abbrev BossB2 : Prop := ∀ p ≥ 5, Nat.Prime p → FermatLastTheoremFor p

/-- The clean B3 vocabulary, definitionally equal to the frozen repository B3. -/
abbrev BossB3 : Prop := IsEmpty FreyPackage

/-- The existing elementary Frey-package reduction from B3 to B2. -/
theorem bossB2_of_bossB3 : BossB3 → BossB2 :=
  FreyPackage.fermatLastTheoremFor_p_ge_5

/-- The existing exponent reduction from B2 to Mathlib's FLT statement. -/
theorem bossB1_of_bossB2 : BossB2 → BossB1 :=
  FermatLastTheorem.of_p_ge_5

/-- The existing adapter from Mathlib's FLT statement to the public positive-natural endpoint. -/
theorem positiveNaturalFlt_of_bossB1 :
    BossB1 → ∀ (a b c : ℕ+) (n : ℕ), n > 2 → a ^ n + b ^ n ≠ c ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem

end FLT.Components.Existing

end
