# FLT-203 provider-neutral boss-chain audit

Task: `task:fg-flt-ra-boss-chain-skeleton-20260716`  
Implementation: `FLT/Components/BossInterface.lean`

## Exact surface

```text
FLT.Components.FreyContradictionInterface
FLT.Components.FreyContradictionInterface.noFreyPackage
FLT.Components.FreyContradictionInterface.fermatLastTheorem
```

The interface contains two abstract predicates on `FreyPackage`, one provider for each predicate,
and their pointwise incompatibility. The first exported theorem derives `IsEmpty FreyPackage`; the
second follows the already-kernel-clean elementary route to the exact Mathlib
`FermatLastTheorem` endpoint.

The module imports only `FLT.Basic.Lemmas` and `FLT.FreyCurve.Basic`. Its elaborated environment does
not contain concrete `B4`, `galoisRep`, Mazur, the Ribet--Wiles provider, the generic
`knownin1980s` axiom, or the admitted torsion declarations.

## Kernel result

`methodology/evidence/contracts/BossInterfaceAudit.lean` reproduces:

```text
noFreyPackage     [propext, Classical.choice, Quot.sound]
fermatLastTheorem [propext, Classical.choice, Quot.sound]
```

`lake build FLT.Components.BossInterface` and the audit file both pass.

## Conditionality

The theorem is explicitly conditional on a term `C : FreyContradictionInterface`. Inhabiting that
structure is equivalent in strength to ruling out every `FreyPackage`; the structure is not an
instance and no provider term exists. This is an integration skeleton, not an unconditional FLT
proof and not progress against G4 by itself.

The later FLT-412 adapter must definitionally bind the abstract irreducibility proposition to the
concrete Frey p-torsion representation and supply both the Mazur and terminal reducibility proofs.
Its semantic definition and kernel axiom closure are separate required audits.

## Review

Fable 5 independently reproduced the build, types, import hygiene, and axiom closures in
`methodology/review/FLT-201-BOSS-INTERFACE-FABLE5.md`. It returned `APPROVE` with no P0/P1 finding.
Its semantic-labelling P2 was resolved by explicit field documentation.

## Adjudication

`PASS`

The exact FLT-203 acceptance gate is met. No provider implementation or admitted concrete data is
hidden in the interface type, and every exported theorem is both standard-axiom-only and explicitly
labelled conditional.
