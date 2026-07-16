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

The next formal-to-concrete tranche is also kernel-clean:

- `TateCurve.c₄Formal_eq_one_sub_mul_a₄Formal` and `TateCurve.evalInt_c₄Formal`;
- `TateCurve.evalInt_invOfUnit_c₄Formal_pow_three`;
- `TateCurve.weierstrassJInvFormal` and its evaluation law;
- `WeierstrassCurve.tateCurve_c₄_eq_evalInt`; and
- `WeierstrassCurve.tateCurve_j_inv_eq_evalInt_weierstrassJInvFormal`.

These identify the reciprocal concrete Tate `j`-invariant with evaluation of the
Weierstrass-derived formal series. Their exact shared axiom closure is
`[propext, Classical.choice, Quot.sound]`.

The remaining construction leaf, `exists_variableChange_tateCurve`, now exposes two exact
mathematical boundaries. First it needs the integral formal identity

```lean
TateCurve.weierstrassDiscriminantFormal = TateCurve.ΔFormal
```

equating the Lambert-series discriminant polynomial with the Euler product
`X * (∏' m, (1 - X ^ (m + 1))) ^ 24`. Mathlib has complex-analytic modular-form versions, but no
bridge to these integral formal series. Once this identity is supplied, the existing substitution
inverse can finish the analytic `j(tateCurve q)` round-trip. Second, the pinned same-`j` theorem
assumes `IsSepClosed k`, while the needed variable change must descend to the original local field.
Existing repository descent infrastructure covers fixed data over a quadratic extension, not this
separable-closure descent.

`FLTMethodology/Probes/TateDeltaFormalRoute.lean` makes the first boundary exact. It proves,
with the standard axiom trio, that the integral `E₄` and `E₆` series map to Mathlib's complex
q-expansions, that `weierstrassDiscriminantFormal` maps to the modular discriminant q-expansion,
and that the sole remaining bridge

```lean
PowerSeries.map (Int.castRingHom ℂ) TateCurve.ΔFormal =
  UpperHalfPlane.qExpansion 1 CuspForm.discriminant
```

implies `weierstrassDiscriminantFormal = ΔFormal` by injectivity. Pinned Mathlib supplies both the
analytic Euler-product theorem and the formal convergent product, but no declaration relating the
analytic q-product's Taylor series to that formal t-product.

The same probe proves the generic coefficient-stabilisation theorem

```lean
coeff k (∏' n : ℕ, ((1 : R⟦X⟧) - X ^ (n + 1))) =
  coeff k (∏ n ∈ Finset.range k, ((1 : R⟦X⟧) - X ^ (n + 1)))
```

for every Hausdorff topological commutative coefficient ring. Its axiom closure is
`[propext, Classical.choice, Quot.sound]`. Thus the formal infinite product no longer contributes an
uncontrolled limit at an individual coefficient: every coefficient reduces to a finite algebraic
product.

`FLTMethodology/Probes/TateDeltaAnalyticBridge.lean` now closes that analytic boundary. It uses
Mathlib's locally uniform convergence of the Euler product, iterates the theorem that derivatives
of locally uniform holomorphic limits converge, and proves that every formal-product coefficient is
the normalized derivative of the analytic product at zero. It then transports multiplication and
the twenty-fourth power through the Taylor series and obtains, with the standard axiom trio,

```lean
PowerSeries.map (Int.castRingHom ℂ) TateCurve.ΔFormal =
  UpperHalfPlane.qExpansion 1 CuspForm.discriminant
```

Consequently the methodology probe also proves the integral identity

```lean
TateCurve.weierstrassDiscriminantFormal = TateCurve.ΔFormal
```

Both declarations have axiom closure `[propext, Classical.choice, Quot.sound]`. They remain outside
the verified FLT root and therefore do not by themselves remove any of the nine admissions in
`TateCurve.lean`; provider migration and downstream consumption are separate gates.

The formal-product/q-expansion obstruction is therefore discharged at methodology-probe level. The
next exact prerequisites are migration of this theorem into a verified provider, evaluation of the
resulting substitution identity, and descent of the variable change to `k`.

Nine admissions remain in `TateCurve.lean`, including the separate Weil-pairing terminal.
