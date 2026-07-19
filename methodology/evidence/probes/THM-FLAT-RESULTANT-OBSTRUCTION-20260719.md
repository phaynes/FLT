# THM-FLAT-RESULTANT obstruction evidence

- Task: `task:ca-flt-thm-flat-resultant-e2e-20260719`
- Producer: `agent:gpt56-xhigh-flat-resultant-producer`
- Producer lane: `gpt-5.6`, `xhigh`
- Branch: `codex/ca-flt-thm-flat-resultant-e2e-20260719`
- Inspected base: `21237fbf281cabfd2afae19fb4841dab0e806d0c`
- Contract: `methodology/control/theorem-contracts.ndjson:8`
- Declaration: `WeierstrassCurve.resultant_Φ_ΨSq`
- Disposition: obstruction report; theorem closure is not claimed

## Exact target state

`FLT/KnownIn1980s/EllipticCurves/Flat.lean:245` states the universal identity over every
commutative ring and every nonzero integer `n`. Its proof at line 251 is a direct `sorry`.
The adjacent normalization lemma reduces the explicitly padded resultant to Mathlib's default
resultant. The adjacent coprimality theorem is independently proved by passage to a maximal-ideal
quotient and `WeierstrassCurve.isCoprime_Φ_ΨSq_field`.

No source change was made to the target theorem because the available results do not prove its
stronger equality.

## Local source and metadata search

The pinned dependency is Mathlib commit
`a3364faec42918fcd84a03a255b50570129f9ead`. Searching that source, the FLT tree, and the vendored
HasseWeil slice found no exact universal division-polynomial resultant theorem:

```text
rg -n --hidden --glob '*.lean' \
  'resultant.*(Φ|ΨSq)|(Φ|ΨSq).*resultant|resultant_Φ_ΨSq' \
  .lake/packages/mathlib/Mathlib FLT HasseWeil vendor 2>/dev/null
```

The only exact-name declaration is the admitted target itself. The usable pinned APIs establish:

- `map_Φ` and `map_ΨSq`;
- degree and leading-coefficient formulas for `Φ n` and `ΨSq n`;
- `Polynomial.resultant_map_map` and standard degree/product identities;
- the padding equality `resultant_Φ_ΨSq_explicit_eq_default`;
- field coprimality when the discriminant is nonzero, and hence the independently proved
  `isCoprime_Φ_ΨSq` when the discriminant is a unit.

These facts show nonvanishing/coprimality on nonsingular fibres. They do not determine the
universal resultant's divisor multiplicity or its constant unit.

Repository history records the same boundary at commit `c4db00f9d89593734a86cf546cc99bea36776cd2`:
the padded/default normalization is kernel-clean, while the universal
`Res(Φ_n, Ψ_n²) = ±Δ^k` identity is absent.

## Missing proof ingredients

A sound universal proof still needs a theorem or development that:

1. works over a universal Weierstrass coefficient ring and proves that the resultant is supported
   exactly on the discriminant divisor;
2. computes the discriminant multiplicity as `(n⁴ - n²) / 6` (coprimality off the divisor does
   not determine this multiplicity);
3. proves that the remaining universal unit is `1` or `-1`, not merely a unit after localization;
4. transports that universal equality to an arbitrary commutative ring using the existing map
   lemmas.

The recurrence definitions of `preΨ`, `ΨSq`, and `Φ` do not make this a finite `ring` or `simp`
calculation for symbolic `n`; closing it directly would require a new induction/resultant or
invariant-theory development. No counterexample was found, so this is an implementation/source
obstruction rather than evidence that the mathematical statement is false.

## Executable evidence

Targeted build:

```text
$ lake build FLT.KnownIn1980s.EllipticCurves.Flat
✔ [2553/2556] Built HasseWeil.Foundation.Auxiliary.Universal
✔ [2554/2556] Built HasseWeil.Foundation.Auxiliary.EllipticDivisibilitySequence
✔ [2555/2556] Built HasseWeil.Foundation.Auxiliary.DivisionPolynomial
✔ [2556/2556] Built FLT.KnownIn1980s.EllipticCurves.Flat
Build completed successfully (2556 jobs).
```

Declaration-level audit (`FLTMethodology/Probes/FlatResultantAudit.lean`):

```text
$ lake env lean FLTMethodology/Probes/FlatResultantAudit.lean
'WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.resultant_Φ_ΨSq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The build is green because the target remains admitted. The exact target audit is not
kernel-clean. Consequently the theorem contract remains `proof_status: admitted` and
`review_status: unreviewed`; no kernel-clean review package was created.

## Recommended next contract

Replace the current `direct-lean-proof-from-existing-polynomial-api` resource assumption with a
separate prerequisite for the universal division-polynomial resultant formula, backed either by
an exact formalized source theorem or by an explicit universal-invariant/resultant development.
Only after that prerequisite is kernel-clean should `THM-FLAT-RESULTANT` be re-dispatched for the
short base-change assembly and independent axiom/build review.
