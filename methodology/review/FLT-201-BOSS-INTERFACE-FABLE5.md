# FLT-201 boss-interface review

Date: 2026-07-16  
Reviewer: Claude Fable 5 through `kg_model_bridge`  
Reviewed source commit: `324fa8314835c1eeccf5dd09c1c8b5fb008b7c70`  
Mode: independent, read-only, bounded signature and kernel review

## Verdict

`APPROVE`

The reviewer independently reproduced:

```text
lake build FLT.Components.BossInterface
lake env lean methodology/evidence/contracts/BossInterfaceAudit.lean
```

and observed:

```text
FLT.Components.FreyContradictionInterface.noFreyPackage
  [propext, Classical.choice, Quot.sound]

FLT.Components.FreyContradictionInterface.fermatLastTheorem
  [propext, Classical.choice, Quot.sound]
```

The endpoint was confirmed to be the unshadowed Mathlib `FermatLastTheorem`. The elaborated import
environment contained none of `knownin1980s`, `FreyPackage.mazur`,
`WeierstrassCurve.galoisRep`, `FLT.Bosses.B4`, `FLT.Bosses.B4_proof`, `flt`,
`WeierstrassCurve.n_torsion_finite`, `WeierstrassCurve.n_torsion_card`,
`FreyCurve.torsion_not_isIrreducible`, or `GaloisRep.IsIrreducible`.

## Findings

There were no P0 or P1 findings.

The principal P2 finding was semantic labelling. The two predicates are deliberately unconstrained:
inhabiting the structure is exactly as strong as ruling out every `FreyPackage`, but the type does
not itself force the predicate named `Irreducible` to mean irreducibility of the concrete Frey
Galois representation. Field documentation now makes this explicit. The concrete adapter therefore
requires both a kernel axiom audit and a semantic audit of the predicate definitions.

The review also noted that the audit evidence was not part of the reviewed commit. It is banked with
this report.

## Task-gate adjudication

`PASS`

The shared vocabulary elaborates without generic `knownin1980s`, `sorryAx`, provider imports, or
admitted data hidden in its interface types. All five fields are consumed by the integration proof.
Adding a concrete representation field now would reintroduce the admitted torsion dependency, so
that semantic binding is correctly deferred.

## Next adapter obligation

The later concrete adapter must define the abstract irreducibility predicate to be definitionally
the concrete proposition

```text
GaloisRep.IsIrreducible ((P.freyCurve).galoisRep P.p P.hppos)
```

and supply both the Mazur irreducibility proof and the Ribet--Wiles non-irreducibility proof with a
standard-axiom-only closure. Until that adapter exists and passes both audits, the current theorem is
explicitly conditional and is not an FLT completion claim.
