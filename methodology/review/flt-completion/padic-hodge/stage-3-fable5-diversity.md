# Stage 3 Fable 5 diversity design — p-adic Hodge

## Verdict: DESIGN-VIABLE

All checks ran in temporary files against Lean `4.32.0-rc1` and Mathlib `a3364fa`. No repository
file, task state, obligation, or axiom was changed by the reviewer.

## Machine-checked Tier-1 vocabulary

The following units elaborated with exactly `[propext, Classical.choice, Quot.sound]`:

- `AbstractWeightData`, indexed by global embeddings
  `F →+* AlgebraicClosure ℚ_[ell]`;
- regularity as rank/cardinality plus `Multiset.Nodup` at every embedding;
- binary `HodgeTateWeightsMatch`;
- the exact Fontaine–Laffaille interval
  `Set.Icc a (a + (ell : ℤ) - 2)` with one global `a`;
- `EllUnramifiedInIntegers` using
  `Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ell : ℤ)})`;
- rho-free `AbstractWeightLocalData`;
- a kernel-clean contragredient `GaloisRepDual` defined by
  `sigma ↦ (rho sigma⁻¹).dualMap`;
- guard lemmas showing `2 < ell` is required for `{-1,0}` to lie in the selected interval and
  regularity rejects `{0,0}`.

The persisted first probe must contain only this vocabulary and the dual construction. It must not
name crystalline or Hodge–Tate extraction placeholders.

## New mathematical findings

### Flatness must be on the integral model

`GaloisRep.IsFlatAt` typechecks over a field because a field is a local ring, but the resulting
condition is essentially vacuous. The future bridge must use `rho0 : GaloisRep F O V0` for
flatness, expose `iso : E ⊗[O] V0 ≃ₗ[E] V` and
`compat : (rho0.baseChange E).conj iso = rho`, and conclude crystallinity/weights at `rho`.

### The determinant convention forces the sign

The repository consumers use `det rho = epsilon`. Under Taylor's normalization
`HT(epsilon) = -1`, the weight-two multiset at `rho` must be `{-1,0}`. The dual
`GaloisRepDual rho`, corresponding to the etale-H1 side, has `{0,1}`. This is a forced consistency
condition, not a cosmetic convention.

The selected critical route states the source boundary at `rho` with `{-1,0}` and keeps the
dual-weight/crystallinity transport theorems as explicit audit bridges. A future weight-sum equals
determinant-weight theorem must guard against sign regression.

### Automorphic at-ell unramifiedness stays in RACAR

`IsAutomorphicOfLevel` only controls places away from ell. The RACAR interface must carry both the
automorphic weight datum and explicit `pi_v` unramifiedness for every `v | ell`. Crystallinity is not
Galois unramifiedness at ell.

## Honest remaining gaps

- G1: `GaloisRep.IsCrystallineAt`, requiring actual period-ring infrastructure;
- G2: Hodge–Tate weight extraction under the pinned sign convention;
- G4: the finite-flat to crystalline weight-two theorem, the dominant risk;
- G5: global embedding to ell-adic place API used inside weight extraction;
- G6/G6-prime: dual transport for weights and crystallinity;
- G7: sum of weights equals determinant weight.

No placeholder propositions or citation-backed theorems are permitted for these nodes.

## Next probe

Create `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`, register it in
`FLTMethodology.lean`, and include only the global weight data, regularity/matching/interval,
field-unramifiedness, `AbstractWeightLocalData`, the interval/regularity guards, and
`GaloisRepDual`, with complete standard-trio audits.

The integral/generic-fibre bridge is persisted only after the coefficients probe lands. The Tier-1
weight vocabulary itself is independent of coefficients.
