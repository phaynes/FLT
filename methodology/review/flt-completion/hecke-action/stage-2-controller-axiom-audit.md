# Controller axiom audit — accepted Hecke algebraic surface

Date: 2026-07-18 AEST  
Task: `task:fg-flt-ra-math-source-design-20260716`

## Scope

The GPT review proposed a first landable algebraic surface containing
`heckeModule_finite_over_heckeAlg`. A controller-side temporary probe combined that surface and
checked its exact axiom dependencies. No repository Lean source was changed by the probe.

Temporary probes:

- `/tmp/HeckeAcceptedSurfaceProbe.lean`
- `/tmp/HeckeFiniteRouteAudit.lean`

Both compiled from the repository root with `lake env lean` after the second probe's expected
signature corrections.

## Result

The algebraic definitions and helper declarations elaborate, but the finite-over-Hecke instance is
not T1/standard-trio clean:

```text
'FLT.MethodologyProbe.HeckeAction.heckeModule_finite_over_heckeAlg' depends on axioms:
[propext, Classical.choice, Quot.sound, isFiniteRelIndex_stabilizer]
```

Importing `FLT.AutomorphicForm.QuaternionAlgebra.FiniteDimensional` does not remove that dependency.
The alternative double-coset theorem itself is standard-trio clean:

```text
'TotallyDefiniteQuaternionAlgebra.finite_doubleCoset' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

but the live `U₁` sufficiently-small instance uses
`LevelStruct.isFiniteRelIndex_Δ`, whose proof is exactly the authorized named quaternion T2
boundary `TotallyDefiniteQuaternionAlgebra.isFiniteRelIndex_stabilizer`. That instance is consumed by
the finite automorphic-form module construction. Therefore selecting the theorem-based
`LevelStruct.IsFinite` instance alone cannot remove the named axiom.

Other accepted helper declarations audited in the combined probe had only the standard trio (or a
subset):

- `IsCompleteLocalHeckeFactor` — standard trio;
- `surjective_of_hits_hecke_generators` — standard trio;
- `RToTActionData` — `propext`, `Quot.sound`;
- `deformationClassifyingMap` — standard trio.

## Disposition

Do not label the U₁ finite-over-Hecke unit T1-clean. It is kernel-clean only relative to the already
registered named quaternion T2 assumption. The Fable reconciliation must either:

1. keep the dependency explicit and classify this unit as T2-dependent until the quaternion boundary
   is discharged at T3; or
2. provide and probe a genuinely standard-trio proof of the sufficiently-small fact without consuming
   `isFiniteRelIndex_stabilizer`.

This audit does not refute the Hecke design. It corrects the assurance classification before any
signature is promoted.
