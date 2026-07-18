# Controller bounded build — tame-residue U1/U2

Date: 2026-07-18 (Australia/Sydney)

Verdict: `BOUNDED-U1-U2-KERNEL-GREEN — BUILD REVIEW REQUIRED`.

## Persisted declarations

The production module `FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup` now contains:

1. `AddSubgroup.isClosed_inertia`;
2. `isClosed_localInertiaGroup`;
3. `localTameAbelianInertiaGroup_le_localInertiaGroup`.

The methodology audit is `FLTMethodology/Probes/TameResidueBoundary.lean`, imported by
`FLTMethodology.lean`.

No `tameResidueChar`, kernel theorem, reciprocity theorem, historical axiom, source locator, or
consumer-signature change was added. `FLT-TAME-RESIDUE` remains a definition gap; U3 roots-of-unity
reduction is the first open arithmetic unit.

## Bounded placement repair

The first placement put U2 before this module's `CharZero Kᵥ` and `Algebra.IsInvariant` instances.
The production build therefore could not synthesize `IsGalois Kᵥ (Kᵥᵃˡᵍ)`. The statement and proof
were unchanged and moved after those instances. This single placement-only repair then compiled.

## Kernel evidence

Commands:

```text
lake build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
  FLTMethodology.Probes.TameResidueBoundary
lake env lean FLTMethodology/Probes/TameResidueBoundary.lean
```

Result: exit 0.

```text
'AddSubgroup.isClosed_inertia' depends on axioms: [propext, Classical.choice, Quot.sound]
'isClosed_localInertiaGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'localTameAbelianInertiaGroup_le_localInertiaGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A forbidden-token scan across the changed production module and probe found no `sorry`, `sorryAx`,
`knownin1980s`, `axiom`, `admit`, `unsafe`, or `native_decide` occurrence.

## Graph evidence

The complete-schema `FLT-TAME-RESIDUE` row is installed as `definition-gap`, bound to `FLT-304 /
class-field`, and added to W03. Graph regeneration reports:

```text
obligations=55 edges=102 critical=55 cycles=0
```

The exact four new edges are:

- `E-TAME-RESIDUE-SGOOD-DEF`;
- `E-TAME-RESIDUE-CBASE`;
- `E-TAME-RESIDUE-SGOOD-SELECTED`;
- `E-TAME-RESIDUE-SUPPORT-DEFORMATION`.

There is no edge to `FLT-CLASS-FIELD` or `FLT-LOCAL-GALOIS` and no reciprocity edge.

## Remaining gate

An independent Opus build review must inspect the production placement, exact theorem types, axiom
surfaces, graph ownership, and absence of scope creep. Until it passes, this tranche is
`built-review-pending`; neither `FLT-TAME-RESIDUE` nor `FLT-CLASS-FIELD` is promoted.
