# FLT-TATE-TORSION AINTLIB integration audit

Date: 2026-07-17  
Source-design task: `fg-flt-ra-math-source-design-20260716`  
Provider task: `fg-flt-elliptic-torsion-card-provider-20260717`  
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

The reviewed module conversion and FLT provider are retained in the main worktree and prove the
complete frozen `n_torsion_card` contract. AINTLIB's torsion target builds under FLT's pinned Lean
`v4.32.0-rc1` and Mathlib `a3364faec42918fcd84a03a255b50570129f9ead`; no toolchain upgrade is
required.

The exact imported target slice contains 52 HasseWeil modules and 27,204 source lines after two
unused admitted declarations and their consumer-free derived declarations are removed. A raw
source scan of those 52 modules finds no executable `sorry`, `admit`, `axiom`, `unsafe`, or
`native_decide`. The target rebuild succeeds, and
`HasseWeil.WeilPairing.TorsionGeometric.card_torsion_ell` still audits to exactly the standard
axiom trio.

## Complete production bridge

The production integration proves the following chain:

1. `fltNTorsionEquivAintlibTorsion` identifies FLT's `E.nTorsion n` subtype with AINTLIB's
   `torsionSubgroup E.toAffine (n : ℤ)`.
2. `flt_n_torsion_card_of_aintlib` transports AINTLIB's theorem to FLT over an algebraically
   closed field.
3. The tracked methodology theorem `prePsi_separable_of_n_torsion_card` recovers separability of
   `E.preΨ' n` from that exact algebraically closed torsion count.
4. `prePsi_separable_of_aintlib_torsion_card` base-changes to `AlgebraicClosure k`, applies steps
   2 and 3, and descends separability with `Polynomial.separable_map`.
5. `flt_n_torsion_card_sepClosed_of_aintlib` applies the existing native root/fibre-count theorem
   and proves the frozen `[IsSepClosed k]` result.

Every theorem in this bridge audits to:

```text
[propext, Classical.choice, Quot.sound]
```

This resolves both previously identified technical mismatches. The legacy sources can be converted
to Lean modules mechanically, and the `IsAlgClosed`/`IsSepClosed` gap is bridged without assuming
that a separably closed field is algebraically closed.

## Production retention and compatibility controls

The provider task discharged the former governance and dependency boundary as follows:

1. the exact 52-module slice is retained under `vendor/HasseWeil`;
2. the mechanical module conversion, promoted helper visibility, removed consumer-free admissions,
   and collision-avoiding field-theorem rename are recorded in `vendor/HasseWeil/PROVENANCE.md`;
3. copyright and Apache-2.0 licence provenance are retained with the sources; and
4. the two frozen provider declarations and their dimension, Galois-representation, and rank
   consumers were rebuilt and axiom-audited.

The first full umbrella build found the name collision between AINTLIB's field-specific
`WeierstrassCurve.isCoprime_Φ_ΨSq` and FLT's commutative-ring theorem of the same name. The
retained field theorem is compatibility-named `isCoprime_Φ_ΨSq_field`; its statement and proof
body are unchanged. Full `FLT` and `FLTMethodology` builds pass after this repair.

## Reusable mathematical information

AINTLIB independently confirms the intended mathematical route and supplies useful designs for:

- the elliptic formal group and the linear coefficient of multiplication;
- field-general separability of multiplication by an integer prime to the characteristic;
- unramifiedness at torsion points; and
- kernel cardinality over an algebraically closed field.

The local theorem `prePsi_separable_of_n_torsion_card` supplies the crucial reverse direction:
exact torsion cardinality over an algebraic closure forces the division polynomial to be separable.
It reuses the already-proved characteristic-safe detector, pointwise coprimality, fibre
multiplicities, parity split, and degree formula. This avoids constructing a second elliptic formal
group solely to repair the external theorem's stronger field assumption.

## Selected integration

1. Retain and independently review the exact 52-module converted slice, then migrate
   `n_torsion_finite` and `n_torsion_card` through the proved bridge. This is the shortest route
   already demonstrated against the frozen toolchain.
2. Publish a pinned module-converted AINTLIB fork and depend on its audited torsion target rather
   than vendoring the slice.
3. Port a minimal, source-attributed subset of AINTLIB's formal-group/unramified proof into a
   native FLT module. This requires a fresh dependency-closure and licence/provenance audit.
4. Continue the native dual-number/formal-group adapter route. It remains mathematically valid but
   is no longer the smallest demonstrated route to the frozen provider theorem.

Option 1 was selected and implemented under the provider task. `FLT-TATE-TORSION` is now integrated,
its graph row is closed, and its retained regression boundary is the full build, source manifest,
zero-admission scan, and consumer axiom audit.
