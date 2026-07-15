# Frozen baseline

This experiment is frozen at upstream commit
`ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b`, authored on 14 July 2026. The
methodology branch is not allowed to silently rebase its evidence or theorem contracts onto a
later upstream commit.

## Toolchain

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- Lean: `4.32.0-rc1`, commit `b4812ae6aed099a37d3c3d26ca0a5273b2dc17d7`
- Lake: `5.0.0-src+b4812ae`
- Mathlib: `a3364faec42918fcd84a03a255b50570129f9ead`

## Reproduction commands

From the repository root:

```sh
git rev-parse HEAD
git status --short
lake build
lake env lean methodology/evidence/baseline/BaselineAudit.lean
rg -n '\bsorry\b' FLT FermatsLastTheorem.lean FLT.lean -g '*.lean'
rg -n '^\s*knownin1980s\s*$' FLT -g '*.lean'
```

The source census is supplementary. The Lean output from `#print axioms` and `#print sorries` is
authoritative for a declaration's dependency closure.

## Frozen theorem contracts

The public terminal is:

```lean
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x ^ n + y ^ n ≠ z ^ n
```

It is derived from:

```lean
theorem flt : FermatLastTheorem
```

through the current boss spine `B4_proof → B3_proof → B2_proof → B1_proof → flt`.

## Reproduced state

- Frozen Git object: present and checked out on
  `methodology/varro-proof-program-20260716`.
- Fork relationship: `phaynes/FLT` is a public fork of `ImperialCollegeLondon/FLT`.
- Verified-root source census: 59 executable-looking `sorry` sites.
- Direct `knownin1980s` tactic uses: 2.
- `B4_proof`: admitted.
- B5 and B6 route: described in source comments and the blueprint; the four major B6-stage
  theorem statements exist but are admitted, while the exact modularity-lifting and
  potential-modularity programmes are not yet represented as an integrated Lean route.

The frozen checkout completed a fresh `lake build` successfully across 8,917 jobs. The exact
declaration-level result is recorded in `methodology/evidence/baseline/RESULTS.md`. In particular,
the public terminal and `flt` both depend on
`[knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]`; `B4_proof` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`. This reproduces the baseline but does not make
the current proof kernel-clean.
