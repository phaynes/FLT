# FLT tame-residue baseline at the current trusted chain

Date: 2026-07-30

Task: `task:ca-flt-tame-residue-completion-20260730`

Branch: `codex/ca-flt-tame-residue-completion-20260730`

Base: `67cddb6b0ce0cffdb2810320d39d8d2e7e9d1bd5`

## Reproduced state

```text
lake -H build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
  FLTMethodology.Probes.TameResidueBoundary
Build completed successfully (3443 jobs).
```

```text
lake -H build FLT FLTMethodology
Build completed successfully (9045 jobs).
```

Every declaration printed in `FLTMethodology.Probes.TameResidueBoundary` audits to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Corrected implementation boundary

The live Lean source is ahead of the stale control description. It already contains:

- the full monoid hom `tameResidueChar`;
- the elementary inclusion from the repository tame proxy to the mapped kernel;
- root lifting for integral units fixed by inertia;
- `TameKummerDecomposition` and `FixedFieldUniformizerDecomposition`;
- the implication from the fixed-field uniformizer provider to the Kummer decomposition;
- the reverse inclusion conditional on that decomposition; and
- the exact kernel equality conditional on `FixedFieldUniformizerDecomposition`.

These are genuine standard-trio Lean results, but the unconditional provider has no witness. The
single deepest remaining leaf is the value-group/uniformizer decomposition for the inertia fixed
field. The control graph must not mark `FLT-TAME-RESIDUE` proved until that provider and the
unconditional exact kernel theorem are built and independently reviewed.
