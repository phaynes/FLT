# Frozen baseline results

The following results were reproduced from upstream commit
`ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b` on 16 July 2026.

## Build

Command:

```sh
lake build
```

Result: success, 8,917 jobs.

## Declaration audit

Command:

```sh
lake env lean methodology/evidence/baseline/BaselineAudit.lean
```

Exact axiom closures:

```text
'PNat.pow_add_pow_ne_pow' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
'flt' depends on axioms: [knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]
'FLT.Bosses.B4_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The transitive `#print sorries` audit for each terminal reports two load-bearing admissions:

```text
WeierstrassCurve.galoisRep has sorry of type
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)
FLT.Bosses.B4_proof has sorry of type
  FLT.Bosses.B4
```

The separate source census is 59 executable-looking `sorry` sites. The difference is expected:
many admitted declarations are not currently in the terminal dependency closure, while major
future programmes are absent rather than represented by `sorry`.

## Methodology scaffold

Commands:

```sh
lake build FLTMethodology.Scaffold \
  FLTMethodology.Probes.ExistingContracts \
  FLTMethodology.Probes.LibraryMatches
lake env lean FLTMethodology/Scaffold.lean
```

Result: success. The scaffold contains exactly four ledgered admissions outside the verified
`FLT` root. Its successful elaboration validates interfaces only; it is not proof progress.
