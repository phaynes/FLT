# Stage 12 prompt — Fable 5 tame-residue diversity repair

Difficulty 10. Required conditional diversity pass after a substantive GPT review. Work read-only:
do not edit Lean, control, graph, source, review, or task files. Do not mutate the proposed graph.

Read:

- `methodology/review/flt-completion/class-field/stage-9-prompt-opus48-tame-graph-design.md`
- `methodology/review/flt-completion/class-field/stage-10-opus48-tame-graph-design.md`
- `methodology/review/flt-completion/class-field/stage-11-gpt56xhigh-tame-graph-review.md`
- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`
- `FLT/Deformations/LiftFunctor.lean`
- `FLT/ModularityLifting/Conditions.lean`
- `FLT/GaloisRepresentation/Automorphic.lean`
- the exact current obligation and graph-owner records for `FLT-SGOOD-DEF`,
  `FLT-SUPPORT-DEFORMATION`, `FLT-SGOOD-SELECTED`, `FLT-CBASE`, and `FLT-LOCAL-GALOIS`.

Produce an independent corrected design, not an edit of the Opus artifact. It must:

1. independently verify or refute the standalone T1 `FLT-TAME-RESIDUE` ownership decision;
2. preserve the exact distinction `P_v ≤ J_v ≤ I_v`, with no claim that wild inertia is
   excluded and no universal strictness claim;
3. verify the four downstream owner edges and prove that no upstream dependency or reciprocity edge
   is required;
4. test the exact signatures for `isClosed_localInertiaGroup`, containment,
   `tameResidueChar`, and the kernel characterization with temporary Lean probes;
5. determine the smallest proof of `isClosed_localInertiaGroup` available in this pin, including
   whether it follows from a continuous residue action, a closed fixing subgroup, or a closed ideal
   inertia theorem; give the exact missing lemma if it does not close;
6. test the containment proof with closedness supplied and identify every residual after it;
7. give a source-faithful elementary construction plan for the tame character that does not invoke
   local class-field reciprocity;
8. keep the source locator gated: do not invent a Serre proposition or page number and do not add
   `SRC-026` without primary visual evidence;
9. classify the audit-only probe as signature evidence only;
10. give the exact candidate obligation row, four dependency mutations, completion criteria,
    bounded Lean units, and stop-loss conditions for later Opus synthesis.

Return `DESIGN-VIABLE`, `REVISE`, `UNCERTAIN`, or `REFUTED`. A viable response must include exact
Lean signatures, temporary-probe results, a transitively reduced graph, the first buildable unit,
the first genuine theorem, and the first expected Lean residual. No graph mutation, source
registration, axiom registration, or proof-completion claim is authorized by this pass.
