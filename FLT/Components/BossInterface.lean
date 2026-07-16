/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

public import FLT.Basic.Lemmas
public import FLT.FreyCurve.Basic

/-!
# Provider-neutral FLT boss interface

This file defines the clean integration boundary between the elementary Frey reduction and the
deep arithmetic providers. It deliberately does not import elliptic-curve torsion, concrete Galois
representations, Mazur's theorem, modularity lifting, or any other admitted provider.

The two predicates are abstract because mentioning the repository's current concrete `galoisRep`
inside the interface type would transitively retain `sorryAx` through its still-admitted torsion
finiteness data. Concrete adapters must later prove that the actual Frey representation supplies
both predicates and that they are incompatible.
-/

@[expose] public section

namespace FLT.Components

/--
Provider-neutral contradiction data for every hypothetical Frey package.

The interface is intentionally weaker than a representation-theory API: the boss integration needs
only two provider propositions for each package and a proof that they cannot both hold. Concrete
irreducibility and reducibility meanings belong to a separately audited adapter.
-/
structure FreyContradictionInterface where
  /--
  An abstract proposition supplied by a later adapter. This field alone does not assert or encode
  Galois-representation irreducibility; the concrete adapter must separately be audited to identify
  it definitionally with that proposition.
  -/
  Irreducible : FreyPackage → Prop
  /--
  An abstract proposition supplied by a later adapter. Its concrete reducibility meaning is not
  enforced by this provider-neutral type and must be established at the adapter boundary.
  -/
  Reducible : FreyPackage → Prop
  /-- Provider evidence for the abstract `Irreducible` socket. -/
  irreducible : ∀ P, Irreducible P
  /-- Provider evidence for the abstract `Reducible` socket. -/
  reducible : ∀ P, Reducible P
  /-- The two abstract provider conclusions are incompatible for each hypothetical package. -/
  incompatible : ∀ P, Irreducible P → Reducible P → False

namespace FreyContradictionInterface

/-- A provider-neutral contradiction rules out every Frey package. -/
theorem noFreyPackage (C : FreyContradictionInterface) : IsEmpty FreyPackage := by
  rw [isEmpty_iff]
  intro P
  exact C.incompatible P (C.irreducible P) (C.reducible P)

/--
The exact Mathlib-form Fermat's Last Theorem, conditional only on the explicit provider-neutral
contradiction interface.
-/
theorem fermatLastTheorem (C : FreyContradictionInterface) : FermatLastTheorem :=
  FermatLastTheorem.of_p_ge_5
    (FreyPackage.fermatLastTheoremFor_p_ge_5 C.noFreyPackage)

end FreyContradictionInterface

end FLT.Components

end
