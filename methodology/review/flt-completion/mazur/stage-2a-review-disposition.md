# Independent-review disposition — Mazur T2 boundary

Status: **CORRECTED; READY FOR OPERATOR AUTHORIZATION; NOT AUTHORIZED**.

This disposition preserves the raw Opus 4.8 report but supersedes one false rationale identified by
the independent GPT-5.6 review.

## Withdrawn claim

The Opus report claimed that the broader statement for semistable elliptic curves with full rational
two-torsion and prime `p ≥ 5` is false because semistable curves with rational `p`-isogenies
exist. That is not a counterexample: those examples need not have full rational two-torsion.
Serre's two character cases, together with the odd-degree quotient isogeny, retain the full
two-torsion needed for the Mazur torsion contradiction.

This withdrawn claim is not load-bearing for the proposed specialized T2 boundary. No registered
source justification may repeat it.

## Corrected boundary and placement

The only proposed T2 assumption remains:

```lean
Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

Its implementation placement is fixed as a declaration in `namespace Serre1987`, co-located in
`FLT/FreyCurve/Mazur.lean` immediately before the unchanged `FreyPackage.mazur` consumer. An
external placement probe elaborates and gives the named probe axiom plus exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Parity translation

`FLTMethodology/Probes/MazurParityBoundary.lean` proves, with only the standard axiom trio:

- `((P.a ^ P.p : ℤ) : ZMod 4) = -1`, using `P.ha4` and `P.hp_odd`;
- `((P.b ^ P.p : ℤ) : ZMod 32) = 0`, using `P.hb2` and `P.hp5`.

These are the exact exponentiated parity translations required by Serre 1987 §4.1,
Proposition 6, printed p. 201.

## Remaining authority boundary

No axiom is registered by this disposition. A human operator must separately authorize the exact
name, type, co-located module placement, source locator, parity translation, T2-only scope, and
post-registration axiom audit. The assumption remains forbidden at T3.
