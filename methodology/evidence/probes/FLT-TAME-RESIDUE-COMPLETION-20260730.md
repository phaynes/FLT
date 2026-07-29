# FLT tame-residue completion candidate — controller evidence

Date: 2026-07-30

Obligation: `FLT-TAME-RESIDUE`

Worktree: `/Volumes/second-store/devel/proof-forks/FLT-tame-residue-completion-20260730`

Branch: `codex/ca-flt-tame-residue-completion-20260730`

## Exact declarations

The candidate adds the exact unconditional declarations:

```lean
theorem fixedFieldUniformizerDecomposition :
    FixedFieldUniformizerDecomposition v

theorem localTameAbelianInertiaGroup_eq_ker :
    localTameAbelianInertiaGroup v =
      (tameResidueChar v).ker.map (localInertiaGroup v).subtype
```

No existing provider, consumer, or kernel theorem statement was weakened or renamed.

## Controller forced-hash reproduction

All commands were run by the controller after the proof-mutating builder stopped.

1. `lake -H build FLT.Deformations.RepresentationTheory.FixedFieldUniformizer FLTMethodology.Probes.FixedFieldUniformizerBoundary`
   - exit 0
   - 3,454 jobs
2. `lake -H build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup FLTMethodology.Probes.TameResidueBoundary`
   - exit 0
   - 3,443 jobs
3. `lake -H build FLT FLTMethodology`
   - exit 0
   - 9,047 jobs

The full replay still exposes unrelated pre-existing `sorryAx` in
`FLTMethodology.Probes.TateTorsionTransportAudit`. That admission is outside this tranche and is
not imported by the public FLT theorem. It must not be mistaken for a tame-residue admission.

## Declaration-level axiom audit

The dedicated probe checks every new declaration. Every reported declaration depends on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

In particular:

```text
'fixedFieldUniformizerDecomposition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'localTameAbelianInertiaGroup_eq_ker' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

A prohibited-token scan found no `sorry`, `sorryAx`, or new `axiom` in the production module or
its audit probe. The controller's initial worktree-level `git diff --check` passed before this
packet was added. Fable correctly found that the frozen candidate-range check then failed on three
Markdown hard-breaks in this packet. Those trailing spaces were removed after review; the
corrected-HEAD range check now passes, while the immutable frozen-candidate result remains recorded
as the historical finding. No Lean source was affected.

## Source and promotion boundary

The mathematical route is consistent with the retained independent locator review of Neukirch,
*Algebraic Number Theory*, Chapter II sections 3, 7, and 9. The current worktree does not contain a
locally hash-verified primary-source copy or registered `SRC-026`. Therefore this packet establishes
kernel/build evidence, not source-grounded promotion by itself. Independent mathematical/build
review and an honest source-status decision are still required before updating the obligation.
