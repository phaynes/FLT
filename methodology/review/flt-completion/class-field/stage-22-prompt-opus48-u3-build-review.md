# Independent Opus 4.8 build review — tame-residue U3

ROLE

Act as the independent build reviewer for the bounded U3 tame-residue tranche. Do not edit any
file, commit, push, or promote an obligation. `VERIFY != PRODUCE`.

REPOSITORY

`/Volumes/second-store/devel/proof-forks/FLT`

REVIEW SHA

`3cd3560`

The live branch may contain later control-only review-launch metadata. Before using it, prove that
the three reviewed source/probe paths are byte-identical to `3cd3560`. If they differ, stop with
`NO-RESULT — MOVING SOURCE` rather than reviewing another tranche.

SCOPE

Review only:

- `FLT/Mathlib/RingTheory/RootsOfUnity/ResidueField.lean`;
- the U3 additions in
  `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`;
- `FLTMethodology/Probes/TameResidueBoundary.lean`;
- `methodology/review/flt-completion/class-field/stage-19-opus48-u3-primary-design.md`;
- `methodology/review/flt-completion/class-field/stage-20-gpt56xhigh-u3-review.md`; and
- `methodology/review/flt-completion/class-field/stage-21-controller-u3-bounded-build.md`.

The ten new declarations are:

1. `eq_one_of_pow_eq_one_of_residue_eq_one`;
2. `rootsOfUnity_residue_injective`;
3. `finiteFieldUnitsToRootsOfUnity`;
4. `finiteFieldUnitsToRootsOfUnity_injective`;
5. `finiteFieldUnitsToRootsOfUnity_bijective`;
6. `finiteFieldUnitsEquivRootsOfUnity`;
7. `isUnit_card_sub_one_ICv`;
8. `residueUnitsEquivRootsOfUnity_at_place`;
9. `tameRootsReduction_at_place`; and
10. `tameRootsReduction_at_place_injective`.

REQUIRED CHECKS

1. Inspect every complete proof body and exact type. Check the geometric-sum cancellation argument,
   finite-cardinality bijection, local-place unit proof, residue-field embedding, equivalence
   orientation, and injectivity composition.
2. Confirm the generic declarations belong in the new public reusable module and do not acquire an
   accidental dependency on the FLT namespace or a stronger local-field hypothesis.
3. Confirm the place-specific declarations occur after all instances they consume and before the
   later Frobenius declarations; check their public names and implicit `v` parameter elaborate as
   intended.
4. Run:

   ```text
   lake build FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField \
     FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup \
     FLTMethodology.Probes.TameResidueBoundary
   lake build FLT FLTMethodology
   ```

5. Reproduce `#print axioms` for all ten declarations. PASS requires exactly
   `[propext, Classical.choice, Quot.sound]` for each, with no `sorryAx`, custom axiom, `admit`,
   `unsafe`, `native_decide`, or `knownin1980s`.
6. Confirm no consumer, graph edge, historical-assumption row, source locator, T2 boundary, or
   `localTameAbelianInertiaGroup` definition changed in this tranche.
7. Confirm this establishes U3 residue-field descent/injectivity only. U4 `tameResidueChar`, U5
   Henselian lifting, and U6 kernel equality must remain absent/open; `FLT-TAME-RESIDUE` must remain a
   `definition-gap`.

FAIL-CLOSED RULE

Do not repair anything. A build, type, statement, axiom, source-scope, or boundary failure is
`REVISE` or `REFUTED`, not permission to edit. A tool/runtime failure is `NO-RESULT`, not a negative
mathematical verdict.

REPORT

Return exactly one headline verdict:

- `PASS-BOUNDED-U3-BUILD`
- `REVISE`
- `REFUTED`
- `NO-RESULT`

Then report: reviewed SHA/tree-equivalence check; targeted/full build results; axiom table for all
ten declarations; mathematical audit; public-module/declaration-order audit; unchanged-boundary
audit; and the first exact residual goal for U4. Do not claim the aggregate tame-residue obligation,
G4, or FLT is complete.
