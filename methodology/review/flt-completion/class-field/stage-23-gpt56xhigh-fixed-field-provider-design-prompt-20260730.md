# Repo-only design — close the FLT tame-residue fixed-field provider

Read-only design. Do not edit files, commit, or change task state. Work only from this repository and
its pinned dependencies; do not inspect sibling worktrees or external literature. Return an
implementable proof design, not a narrative survey.

Repository:
`/Volumes/second-store/devel/proof-forks/FLT-tame-residue-completion-20260730`

Frozen design base: `67cddb6b0ce0cffdb2810320d39d8d2e7e9d1bd5`

The current source already constructs `tameResidueChar`, proves the easy kernel inclusion, defines
`FixedFieldUniformizerDecomposition`, proves it implies `TameKummerDecomposition`, and proves the
exact kernel equality conditionally. The only intended mathematical leaf is a proof of:

```lean
FixedFieldUniformizerDecomposition v
```

in `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`.

The base has just reproduced a 3,443-job target build and 9,045-job umbrella build. Every declaration
printed by `FLTMethodology.Probes.TameResidueBoundary` has exactly the standard trio
`[propext, Classical.choice, Quot.sound]`; this does not prove the provider proposition.

Tasks:

1. Inspect the exact definition, its consumers, the local inertia/fixed-field definitions, and the
   pinned Mathlib/repository valuation, integral-closure, finite-extension, ramification, and
   infinite-Galois APIs.
2. Test whether the provider is mathematically correct as stated. Look for any normalization,
   inseparability, integrality, fixedness, or infinite-extension counterexample.
3. Recursively decompose the proof until every leaf is either an existing exact theorem, a small
   Lean proof with named tactics/rewrites, or one explicitly missing reusable library theorem.
4. Give exact proposed Lean declaration signatures in dependency order. Prefer the weakest
   purpose-built bridge over building a full local-class-field framework.
5. Identify whether a finite-subextension route can prove unchanged value group: choose a finite
   extension containing the element, connect fixedness by inertia to ramification index one, then
   use a valuation-lies-over theorem. Name the actual available declarations and check their types.
6. Consider a direct integrality route if it avoids the missing abstract value-group API.
7. State the first bounded implementation slice that should compile, and a stop-loss condition. Do
   not hide the provider or an equivalent value-group theorem in an assumption.
8. State exact targeted build and `#print axioms` probes for every new declaration.

End with one verdict: `IMPLEMENTABLE-NOW`, `IMPLEMENTABLE-AFTER-NAMED-LIBRARY-BRIDGE`, or
`STATEMENT-REPAIR-REQUIRED`, followed by the exact reason.
