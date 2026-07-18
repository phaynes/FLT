# Fable 5 second bounded repair — cyclic base change

Verdict: **DESIGN-VIABLE**.

This is the final bounded diversity repair. It corrects the false fiber statement and the unsupported
universe claim without modifying the frozen public `cyclic_base_change` theorem. It authorizes no
obligation promotion, graph mutation, T2 registration, or production theorem by itself.

## Repaired design

- The claim that all future consumers are `Type 0` is deleted. The only established facts are that
  the frozen theorem has two independent universes, the attempted tensor route is blocked by their
  mismatch, and there is no current Lean application. Future consumer universes remain unknown.
- The false broad `BaseChangeFiberUpToTwist` is deleted. Its replacement,
  `BaseChangeFiberUpToTwistOfIrreducible`, explicitly assumes a finite Galois extension,
  algebraically closed coefficient field, finite-dimensional module, and irreducibility after
  restriction. The signature elaborates with only the standard trio; it is still only an interface.
- The quadratic counterexample `rho = 1 + epsilon`, `sigma = 1 + 1` is retained as a mandatory
  regression. The theorem `not_isIrreducible_trivial_two_dim` proves in the kernel that the repaired
  antecedent excludes it.
- Jacquet--Langlands feeds both forward and descent boundaries. The full open analytic set is:
  forward base change, image/descent, cuspidality, Jacquet--Langlands in both directions, strong
  multiplicity one, and level/conductor compatibility.
- Only four existing structural theorems are presently bank-safe:
  `even_finrank_of_even_base`, `mem_preimageComapFinset_iff`,
  `natCast_notMem_of_mem_preimageComapFinset`, and `heckeAlgebra_algHom_ext`. They are infrastructure,
  not proof of `FLT-CBASE`.
- V1, V2, repaired V5, V8, Q1, Q2, V3, and V4 were replayed with complete binders. V6, V7, and V9
  are removed. `FLT-TAME-RESIDUE` remains an explicit dependency and source risk.

## Kernel evidence and next gate

The four infrastructure theorems, eight definitions, and regression theorem all replayed with
exactly `[propext, Classical.choice, Quot.sound]`. One intermediate regression proof honestly
exposed `sorryAx`; the repaired proof closes the remaining bottom-submodule goal and is clean.

The next bounded gate is a production methodology probe containing exactly those declarations,
followed by targeted build, per-declaration axiom audits, and independent review. `FLT-CBASE` remains
admitted and the two analytic source gates remain open.
