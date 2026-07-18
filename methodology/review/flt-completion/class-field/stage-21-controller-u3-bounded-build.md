# Controller bounded build — tame-residue U3

Date: 2026-07-18 (Australia/Sydney)

Verdict: `BOUNDED-U3-KERNEL-GREEN — BUILD REVIEW REQUIRED`.

## Persisted surface

The new reusable module `FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField` contains precisely the
independently reviewed generic U3 surface:

- `eq_one_of_pow_eq_one_of_residue_eq_one`;
- `rootsOfUnity_residue_injective`;
- `finiteFieldUnitsToRootsOfUnity`;
- `finiteFieldUnitsToRootsOfUnity_injective`;
- `finiteFieldUnitsToRootsOfUnity_bijective`; and
- `finiteFieldUnitsEquivRootsOfUnity`.

`FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup` contains precisely the reviewed
place-specific adapters:

- `isUnit_card_sub_one_ICv`;
- `residueUnitsEquivRootsOfUnity_at_place`;
- `tameRootsReduction_at_place`; and
- `tameRootsReduction_at_place_injective`.

The generic local-ring proof uses unit cancellation after the geometric-sum factorization. The
finite-field equivalence uses the exact `q - 1` cardinality of the source unit group and the
`card_rootsOfUnity` upper bound in the target domain. The place adapter reduces integral roots of
unity into the enlarged residue field and applies the inverse equivalence to obtain an element of
the base residue-field unit group.

This establishes U3 residue-field descent and injectivity. It does not construct the U4 tame
character or prove the U5 Henselian lift or U6 kernel equality.

## Kernel evidence

Targeted command:

```text
lake build FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField \
  FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
  FLTMethodology.Probes.TameResidueBoundary
```

Result: `Build completed successfully (3422 jobs)`.

Full command:

```text
lake build FLT FLTMethodology
```

Result: `Build completed successfully (9035 jobs)`.

The full build emitted existing linter warnings in unrelated vendor and methodology modules. No U3
error occurred.

`FLTMethodology.Probes.TameResidueBoundary` prints the following exact axiom surface for all ten new
declarations:

```text
[propext, Classical.choice, Quot.sound]
```

A forbidden-token scan over the new module, changed production module, and audit probe found no
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or `knownin1980s` occurrence.

## Scope and remaining work

- `localTameAbelianInertiaGroup` is unchanged.
- All consumers and all four graph edges are unchanged.
- No reciprocity declaration, source row, historical assumption, or T2 boundary was added.
- `FLT-TAME-RESIDUE` remains a `definition-gap`.
- U4 `tameResidueChar`, U5 Henselian lifting, U6 kernel equality, and the source gate remain open.

An independent build reviewer must now rebuild the exact commit, inspect the public surface and
declaration order, and reproduce the axiom audits before this U3 tranche is sealed.
