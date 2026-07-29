# Build the FLT tame-residue fixed-field provider

You are the sole proof-mutating builder for this cycle. Work only in the current clean branch and
implement the agreed Stage 25 design. Do not create commits, push, change Helios task state, or edit
attempt/control/graph records; the controller owns those operations. You may edit Lean source and
probe files and run builds. Preserve unrelated work.

Read first:

- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`
- `FLTMethodology/Probes/TameResidueBoundary.lean`
- `methodology/evidence/probes/FLT-TAME-RESIDUE-BASELINE-20260730.md`
- `methodology/review/flt-completion/class-field/stage-23-gpt56xhigh-fixed-field-provider-design-response-20260730.md`
- `methodology/review/flt-completion/class-field/stage-24-fable5-literature-fixed-field-provider-design-response-20260730.md`
- `methodology/review/flt-completion/class-field/stage-25-fixed-field-provider-design-synthesis-20260730.md`
- the full Fable plan at
  `/Users/philiphaynes/.claude/plans/literature-grounded-design-structured-hearth.md`
- the prior kernel-clean probe at
  `/Volumes/second-store/devel/proof-forks/FLT-fixed-field-value-group-20260719/FLTMethodology/Probes/FixedFieldValueGroupBridge.lean`

Target:

```lean
theorem fixedFieldUniformizerDecomposition :
    FixedFieldUniformizerDecomposition v

theorem localTameAbelianInertiaGroup_eq_ker :
    localTameAbelianInertiaGroup v =
      (tameResidueChar v).ker.map (localInertiaGroup v).subtype
```

Use a new production module if it gives a cleaner dependency boundary, but ensure it is imported by
the FLT umbrella and by a dedicated probe. Existing public statement signatures must not change.

## Compiler-gated slices

1. Build the finite integral-closure ring pack and the easy restriction inclusion.
2. Prove the reverse finite-inertia restriction inclusion. The intended construction is:
   arbitrarily lift a finite inertia automorphism; use
   `Ideal.Quotient.stabilizerHom_surjective_of_profinite` for the subgroup fixing the finite field
   to match the lift's infinite residue action; correct the lift by the inverse of that subgroup
   element; show the corrected lift is in `localInertiaGroup` and has the requested restriction.
   Carefully verify multiplication order. Plain `restrictNormalHom_surjective` alone is invalid.
3. Deduce trivial finite inertia for a finite Galois subfield contained in the global inertia fixed
   field; deduce ramification index one and mapped-maximal-ideal equality; factor in the finite DVR.
4. Assemble the provider and unconditional kernel theorem.

Relevant pinned engines include:

- `AlgEquiv.restrictNormalHom_surjective`
- `InfiniteGalois.fixingSubgroup_isClosed` and `fixedField_fixingSubgroup`
- `Ideal.Quotient.stabilizerHom_surjective_of_profinite`
- FLT `isInvariant_integralClosure`, `mulSemiringActionIntegralClosure`, and
  `continuousSMulDiscrete_integralClosure`
- `Ideal.card_inertia_eq_ramificationIdxIn`, `ramificationIdxIn_eq_ramificationIdx`, and
  `ramificationIdx_tower`
- `AddSubgroup.subgroupOf_inertia`
- `IsIntegralClosure.isDedekindDomain`, `.finite`, and `.isFractionRing_of_finite_extension`
- `IsDiscreteValuationRing.TFAE`, `irreducible_of_span_eq_maximalIdeal`, and
  `exists_units_eq_smul_zpow_of_irreducible`
- FLT `adicCompletion.maximalIdeal_eq_span_uniformizer` and `tameUniformizer_valuation`.

Run a targeted build after every slice. At the end run:

```bash
lake -H build FLT.Deformations.RepresentationTheory.FixedFieldUniformizer \
  FLTMethodology.Probes.FixedFieldUniformizerBoundary
lake -H build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
  FLTMethodology.Probes.TameResidueBoundary
lake -H build FLT FLTMethodology
```

If you choose a different module name, adjust the first command explicitly and report it. Add
`#print axioms` probes for every new public theorem. Acceptance is exactly the established standard
trio `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or additional axiom.

Fail closed. If the profinite correction or an actual carrier/instance is unavailable, do not
scaffold over it: identify the smallest exact missing declaration and stop. End with changed files,
build outputs, axiom results, remaining gap if any, and one verdict:
`KERNEL-GREEN-CANDIDATE`, `BOUNDED-SLICE-GREEN`, or `NAMED-BRIDGE-BLOCKED`.
