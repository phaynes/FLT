# FLT-TATE-TORSION AINTLIB integration audit

Date: 2026-07-17  
Task: `fg-flt-ra-math-source-design-20260716`  
External repository: `https://github.com/CBirkbeck/AINTLIB.git`  
Reviewed commit: `b91f668cd447754b83880f353c34e4a1ed236f2c`

## Result

AINTLIB contains a kernel-clean proof of the algebraically closed torsion-cardinality theorem:

```lean
HasseWeil.WeilPairing.TorsionGeometric.card_torsion_ell
  [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
  (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2
```

The declaration built at the reviewed commit and its axiom audit returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

A disposable FLT integration checkout proved both an equivalence between the two torsion
subtypes and the corresponding FLT-style cardinality and rank-two statements. Those probes also
had only the standard axiom trio. AINTLIB's torsion target built under FLT's pinned Lean
`v4.32.0-rc1` and Mathlib `a3364faec42918fcd84a03a255b50570129f9ead`; no toolchain upgrade is
mathematically required.

## Why it was not imported

Two frozen interface mismatches remain:

1. FLT exports `n_torsion_card` under `[IsSepClosed k]`, while AINTLIB's capstone requires
   `[IsAlgClosed k]`. A separably closed field need not be algebraically closed in positive
   characteristic, so this cannot be filled by typeclass inference or an assurance-only cast.
2. FLT source files use Lean's `module` discipline, while the reviewed AINTLIB source files are
   legacy non-`module` files. Lean rejects importing `TorsionCardEll` from
   `FLT/EllipticCurve/Torsion.lean` with:

   ```text
   cannot import non-`module` HasseWeil.HasseBound.WeilPairing.TorsionCardEll from `module`
   ```

The imported AINTLIB closure also reports two unrelated source declarations containing `sorry`.
They do not occur in the axiom closure of `card_torsion_ell`, but a future dependency decision must
state whether assurance is declaration-closure based or package-wide.

The main FLT checkout was restored after the failed packaging probe. No AINTLIB dependency or
provider edit was retained.

## Reusable mathematical information

AINTLIB independently confirms the intended mathematical route and supplies useful designs for:

- the elliptic formal group and the linear coefficient of multiplication;
- field-general separability of multiplication by an integer prime to the characteristic;
- unramifiedness at torsion points; and
- kernel cardinality over an algebraically closed field.

The local methodology now removes the `IsSepClosed`/`IsAlgClosed` mismatch without importing
AINTLIB: `prePsi_separable_of_algebraicClosure_formalGroupAdapter` base-changes the curve and
division polynomial to `AlgebraicClosure k`, applies the algebraically closed infinitesimal
argument there, and descends polynomial separability with `Polynomial.separable_map`.

The remaining proof is the actual geometry-linked algebraic-closure adapter (or an equivalent
direct no-infinitesimal-kernel theorem). The existing `PrePsiFormalGroupAdapter` is a conditional
assembly boundary; its `nSeries_annihilates` field still contains the substantive elliptic claim.

## Integration options

1. Continue the native FLT methodology and prove the concrete algebraic-closure adapter. This
   preserves the current package and module boundary.
2. Create and independently audit a pinned `module`-converted AINTLIB fork, then use only the
   clean declaration closure. This is a packaging project, not a one-line dependency update.
3. Port a minimal, source-attributed subset of AINTLIB's formal-group/unramified proof into a
   native FLT module. This requires a fresh dependency-closure and licence/provenance audit.

Option 1 remains the smallest change to the governed FLT proof programme.
