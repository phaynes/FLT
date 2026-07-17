# Mandatory human gate — Mazur named T2 assumption

Status: **AUTHORIZED by operator philip.haynes on 2026-07-18; applied and independently kernel-gated**.

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
This correction does not change the specialized declaration below. The authoritative correction
overlay is `stage-2a-review-disposition.md`; the raw producer report is retained as review history.

## Exact decision proposed

Authorize, for T2 only, one named historical interface with no generic `knownin1980s` wrapper:

```lean
Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

The proposed module placement is now exact: declare the axiom in `namespace Serre1987`,
co-located in `FLT/FreyCurve/Mazur.lean` immediately before `FreyPackage.mazur`.
`/private/tmp/MazurNamedPlacementProbe.lean` confirms that this placement elaborates and supplies
the consumer definitionally.

The explicit parity translations are now proved in
`FLTMethodology/Probes/MazurParityBoundary.lean`:

- `a^p ≡ -1 (mod 4)` from `P.ha4` and `P.hp_odd`;
- `b^p ≡ 0 (mod 32)` from `P.hb2` and `P.hp5`.

Both declarations audit to exactly `[propext, Classical.choice, Quot.sound]`.

Authorization must approve the exact name, type, co-located placement, source locator, parity
translation and T2-only scope. After registration, the stage audit must show the exact named axiom
plus the standard trio, with no `knownin1980s` or new `sorryAx` on the consumer path. The
assumption is forbidden at T3.

The operator authorization was supplied explicitly on 2026-07-18. Registration and the independent
kernel gate are recorded in stage-4-operator-authorization-and-kernel-gate.md. This authorizes the
named interface at T2 only and does not claim T3 discharge.
