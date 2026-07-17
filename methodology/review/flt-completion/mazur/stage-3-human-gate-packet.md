# Mandatory human gate — Mazur named T2 assumption

Status: **READY FOR A HUMAN DECISION, NOT AUTHORIZED**.

## Evidence already established

- The proposed consumer-specific declaration elaborates in
  `methodology/evidence/probes/MazurNamedInterfaceProbe.lean`.
- Its probe audit is exactly `[propext, Classical.choice, Quot.sound]`.
- GPT-5.6 independently verified the primary locator as Serre (1987), section 4.1,
  Proposition 6, printed page 201, with the underlying Mazur input cited there.
- The existing `galoisRep` dependency is standard-axiom clean.

## Correction required by independent review

The Opus report's claimed counterexample outside the exact Frey specialization is not valid.
Semistability plus full rational two-torsion already supplies the relevant irreducibility route for
prime `p >= 5`. That incorrect rationale must not appear in the registered source justification.
This correction does not change the specialized declaration below.

## Exact decision proposed

Authorize, for T2 only, one named historical interface with no generic `knownin1980s` wrapper:

```lean
Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

Authorization must also approve its module placement and the explicit parity translations
`a^p ≡ -1 (mod 4)` and `b^p ≡ 0 (mod 32)`. After registration, the stage audit must show this exact
named axiom plus the standard trio, with no `sorryAx`. The assumption is forbidden at T3.

No authorization has been inferred or recorded by this packet.
