# FLT tested baseline — 2026-07-19

## Status and authority

This branch is the clean, combined **tested candidate baseline** for supervised
Helios Control testing.  It is not an assertion that FLT is complete, not an
independent mathematical review, and not authorization for an unsupervised or
mutating proof loop.

- Integration task: `task:ca-flt-baseline-handoff-integration-20260719`
- Branch: `codex/flt-tested-baseline-20260719`
- Evidence base / last previously trusted FLT revision:
  `1f6d11caee718028bf783c968511d34865ffd9f0`
- Combined proof tree before this evidence note: `0e0c84c`
- Control mode permitted by this note: one operator-supervised,
  non-mutating shadow cycle only
- Vagrant was not used.

Independent adjudication remains required before this candidate may replace the
previous trusted revision for proof promotion or mutation authority.

## Integrated proof tranches

### Class-field / tame-residue tranche

- Source branch: `task/flt-class-field-proof-20260719`
- Source head: `85a0f22056f2ffb51da54ce50f7ae7b897c56ec7`
- Remote equality: confirmed before integration
- Merge commit: `04b276b`
- Handoff:
  `methodology/review/flt-completion/class-field/implementation-handoff-20260719.md`

The tranche adds the reviewed construction chain leading to the conditional
tame-residue results.  The exact remaining mathematical leaf is
`FixedFieldUniformizerDecomposition`; the aggregate class-field boundary is
therefore still open.

### Tate–Frey tranche

- Source branch: `task/flt-tate-frey-proof-20260719`
- Source head: `160050be2a4ca5c70eb09a739eb299b0c04f3027`
- Remote equality: confirmed before integration
- Merge commit: `0e0c84c`
- Handoff:
  `methodology/review/flt-completion/tate-frey/implementation-handoff-20260719.md`

The tranche proves the component assembly theorem `tateEquivOfComponents` and
the division-polynomial coprimality theorem `isCoprime_Φ_ΨSq`.  The public
`WeierstrassCurve.tateEquiv` still depends on admitted providers and therefore
still audits with `sorryAx`.

## Integration checks

- Both source heads descend directly from the evidence-base revision.
- Both source worktrees were clean, pushed, and equal to their upstream refs.
- Their changed-path sets are disjoint.
- Added lines contain no `sorry`, `admit`, `axiom`, `unsafe`, or
  `native_decide` declaration.
- The relevant existing Tate/Frey closure contains 14 direct admissions:
  `TateCurve.lean` 8, `Flat.lean` 2, `GoodReduction.lean` 1,
  `WeilPairing.lean` 1, and `Frey.lean` 2.

## Kernel and build evidence

The combined tree was checked with the targeted build:

```text
lake build \
  FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
  FLT.KnownIn1980s.EllipticCurves.Flat \
  FLT.KnownIn1980s.EllipticCurves.TateCurve \
  FLT.GaloisRepresentation.HardlyRamified.Frey \
  FLTMethodology.Probes.TameResidueBoundary \
  FLTMethodology.Probes.DivisionPolynomialCoprimeAudit \
  FLTMethodology.Probes.TateUniformizationAssembly
```

The repository umbrella build also completed successfully:

```text
lake build FLT FLTMethodology
Build completed successfully (9035 jobs).
```

The bounded promoted declarations report only the standard dependency set
`[propext, Classical.choice, Quot.sound]`, including:

- the class-field conditional tame-residue declarations in
  `TameResidueBoundary`;
- `WeierstrassCurve.isCoprime_Φ_ΨSq`;
- `assembleTateEquiv`, `nonempty_tateEquiv_of_components`, and
  `tateEquivOfComponents`.

The aggregate public `WeierstrassCurve.tateEquiv` honestly reports
`[propext, sorryAx, Classical.choice, Quot.sound]` because its remaining
providers have not been proved.

## Safe continuation

Helios Control may bind this clean checkout for a supervised read-only shadow
test.  The control report must retain the evidence-base revision separately
from this tested candidate, execute no dispatch, perform no proof-source write,
and leave both mutation and unsupervised-loop authority disabled.  Promotion
requires an independent baseline-delta adjudication plus the existing theorem,
literature, and human-readable review-package gates.
