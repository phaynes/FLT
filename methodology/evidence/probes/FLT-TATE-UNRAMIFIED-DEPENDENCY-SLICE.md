# FLT-TATE-UNRAMIFIED dependency slice

Checkpoint: `1acd636`.

The admitted construction order is:

```text
tateCurveEquiv -------------------+
                                  +--> tateEquiv
exists_variableChange_tateCurve --+
                                        |
                         +--------------+--------------+
                         v                             v
             tateEquiv_baseChange          tateEquiv_galois
                         +--------------+--------------+
                                        v
                             tateEquivSepClosure
                                        |
                         +--------------+--------------+
                         v                             v
             tatePoint_baseChange             tatePoint_galois
                                        |
                                        v
                         weilPairing_tatePoint
```

Four directly consumed Galois-action helpers are now kernel-clean:

- `WeierstrassCurve.qUnitSepClosure_galois`;
- `WeierstrassCurve.zpowers_qUnitSepClosure_galois`;
- `WeierstrassCurve.tateQuotientGalois`; and
- `WeierstrassCurve.tateQuotientGalois_apply`.

Each has axiom closure `[propext, Classical.choice, Quot.sound]`. They construct the action of a
`k`-algebra automorphism on the multiplicative Tate quotient and are consumed by the future
`tatePoint_galois` proof. They do not close an admitted export.

The first ellipticity prerequisite is now kernel-clean:

- `TateCurve.weierstrassDiscriminantFormal` and its constant/linear coefficient laws;
- `TateCurve.evalInt_weierstrassDiscriminantFormal`;
- `WeierstrassCurve.tateCurve_Δ_eq_evalInt`; and
- `WeierstrassCurve.isElliptic_tateCurve`.

Every declaration has axiom closure `[propext, Classical.choice, Quot.sound]`. The proof computes
the polynomial discriminant from the existing formal Tate coefficients and uses
`valuation_evalInt_eq`; it does not assume the still-unproved product-series identity for
`ΔFormal`.

The remaining construction leaf, `exists_variableChange_tateCurve`, still meets an API boundary.
The same-`j` route now has ellipticity, but still needs the analytic `j(tateCurve q)` round-trip.
Moreover, the pinned same-`j` theorem assumes `IsSepClosed k`, while the needed variable change must
descend to the original local field. Existing repository descent infrastructure covers fixed data
over a quadratic extension, not this separable-closure descent.

This is a proof/API obstruction, not a counterexample. The next exact prerequisites are the analytic
`j(tateCurve q)` round-trip and descent of the resulting variable change to `k`.

Nine admissions remain in `TateCurve.lean`, including the separate Weil-pairing terminal.
