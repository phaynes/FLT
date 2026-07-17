OPUS 4.8 BOUNDED DESIGN — CLASS-FIELD TAME-RESIDUE GRAPH OWNERSHIP

Work read-only at difficulty 10. The independently reviewed idele object/type tranche is frozen and
must not be reopened. Determine the smallest exact proof-program repair for the elementary tame
residue boundary identified by the class-field reviews.

Read:

- `methodology/review/flt-completion/class-field/stage-6-opus48-synthesis.md`
- `methodology/review/flt-completion/class-field/stage-7-gpt56xhigh-review.md`
- `methodology/review/flt-completion/class-field/stage-8-opus48-build-review.md`
- `FLT/ModularityLifting/Conditions.lean`
- `FLT/Deformations/LiftFunctor.lean`
- `FLT/GaloisRepresentation/Automorphic.lean`
- `FLT/NumberField/AbsoluteGaloisGroup.lean` and the exact TODO defining
  `localTameAbelianInertiaGroup`
- current proof obligations, graph, source register, and `FLT-AUX-LOCAL-FIELD` ownership.

Deliver:

1. an exact decision: add a new `FLT-TAME-RESIDUE` obligation, reuse an existing obligation, or add
   a direct edge—justify why the other options would misstate the mathematics;
2. the exact Lean declaration(s) and types needed to replace the canonical-kernel TODO and serve the
   three real consumers, distinguishing full inertia from tame abelian inertia;
3. exact graph edges and target stage, including whether class-field/global reciprocity is truly an
   upstream dependency (it should not be unless proved necessary);
4. source ownership and the exact source-locator gate without fabricating proposition numbers;
5. the smallest no-axiom probe buildable now, if any, and the first genuine mathematical goal;
6. migration/consumer steps for `BlueprintSGood.traceOnJ`, `traceConditionFunctor`, and
   `cyclic_base_change.hrhoTame`;
7. counterexamples and stop-losses preventing a generic class-field package, full-inertia/tame
   conflation, or hidden reciprocity assumption.

Return `READY-FOR-GPT-REVIEW`, `REVISE`, or `OBSTRUCTION`. Do not edit, add an axiom, promote an
obligation, fabricate a citation, or treat the current TODO definition as mathematically discharged.
