# Stage 2 GPT-5.6 xhigh independent review — p-adic Hodge

## Verdict: REVISE

The two-tier strategy is sound, but the frozen interface is not yet Lean- or source-exact.

- The abstract weight predicates can elaborate now, but `PadicHodgeData` cannot because it includes
  the absent `IsCrystallineAt` field. The first build unit must instead be a separately named
  abstract weight/local-data bundle; full `PadicHodgeData` remains a definition gap.
- The proposed bridge incorrectly used one integral `rho` for both `IsFlatAt` and crystallinity. The
  pinned API applies flatness to an integral model `rho0`, relates its generic fibre to a
  characteristic-zero `rho`, and concludes crystallinity of `rho` (possibly its dual). A repaired
  signature must expose `O`, `E`, `V0`, `V`, `rho0`, `rho`, scalar extension, and compatibility.
- Taylor indexes weights by global embeddings `F →+* AlgebraicClosure ℚ_[ell]`, not embeddings of a
  completion into its own abstract algebraic closure. The repository's cyclotomic-determinant
  convention also leaves a real `{0,1}` versus dual/sign issue open.
- The source interval is `[a, a + ell - 2]`: exactly `ell - 1` consecutive integers, with one global
  `a` for all embeddings. A diameter of `ell - 1` is not the same condition.
- Unramifiedness of `π_v` for every `v ∣ ell` belongs in the RACAR/source interface and must remain
  explicit. It is not encoded by `IsAutomorphicOfLevel ... empty`.
- Prefer the source-level ramification predicate
  `Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ell : ℤ)})`; a pointwise ramification-index statement
  may be derived later.
- `FLT-MLT-COEFFICIENTS` has not landed. Registering definition gaps does not satisfy the T1 gate;
  no placeholder crystalline predicate or citation-backed theorem is permitted.

## Read-only probe result

On Lean 4.32.0-rc1 / Mathlib `a3364fa`, a corrected data-only bundle using

```lean
(F →+* AlgebraicClosure ℚ_[ell]) → Multiset ℤ
```

together with regularity, pointwise matching, the corrected interval, and
`Algebra.IsUnramifiedIn` elaborated with exactly
`[propext, Classical.choice, Quot.sound]`.

## Next exact probe

Persist `AbstractWeightLocalData`, with no `rho`, `IsCrystallineAt`, `hodgeTateWeightsAt`, or
finite-flat bridge, and audit all declarations with `#print axioms`. Probe the generic-fibre/dual
bridge only after repaired coefficient data lands.

## Typed Fable decision

`KEEP`: difficulty is 10 and this review found substantive statement-level defects in the proposed
Tier-1 bundle, integral/generic-fibre bridge, and weight-duality convention.

This review was read-only. No obligation was promoted.
