# Opus 4.8 independent build review — class-field tame-residue U1/U2

Act as the independent final build reviewer at difficulty 10. Work read-only in
`/Volumes/second-store/devel/proof-forks/FLT` at commit
`dca95b766b94651010f3859b747e0ee19f046abc`. Do not edit repository source, control rows, task state,
or review packets. Temporary Lean audit files outside the repository are allowed; build artifacts
may be refreshed by `lake build`.

Read in full:

- `methodology/review/flt-completion/class-field/stage-15-gpt56xhigh-tame-graph-review.md`;
- `methodology/review/flt-completion/class-field/stage-16-controller-mechanical-correction.md`;
- `methodology/review/flt-completion/class-field/stage-17-controller-u1-u2-bounded-build.md`;
- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`;
- `FLTMethodology/Probes/TameResidueBoundary.lean`;
- the exact `FLT-TAME-RESIDUE`, `FLT-CLASS-FIELD`, source-design, execution, graph, and wave rows.

Independently verify:

1. The exact statements and proof bodies of `AddSubgroup.isClosed_inertia`,
   `isClosed_localInertiaGroup`, and `localTameAbelianInertiaGroup_le_localInertiaGroup`.
2. U1 really proves the closedness required by U2; the placement after the module's `CharZero K_v`
   and `Algebra.IsInvariant` instances is mechanically necessary and changes no mathematical scope.
3. U2 is only subgroup containment. It must not be described as the canonical-kernel theorem,
   reciprocity, a residue-character construction, or closure of U3--U6.
4. Run targeted builds and an umbrella `lake build FLTMethodology`. In a temporary file, `#print
   axioms` all three declarations and require exactly `[propext, Classical.choice, Quot.sound]`.
5. Search the complete dependency paths for `sorryAx`, `knownin1980s`, custom axioms, `admit`,
   `unsafe`, and `native_decide`; distinguish unrelated existing admissions from dependencies of the
   reviewed declarations.
6. Verify the complete-schema graph change: one open `FLT-TAME-RESIDUE` node and exactly four edges
   (`FLT-SGOOD-DEF`, `FLT-CBASE`, `FLT-SGOOD-SELECTED`, `FLT-SUPPORT-DEFORMATION` consuming it), with
   no edge to `FLT-CLASS-FIELD` or `FLT-LOCAL-GALOIS`, 55 nodes, 102 edges, and no cycle.
7. Confirm `FLT-TAME-RESIDUE` remains a definition gap and `FLT-CLASS-FIELD` remains open. No T2
   source promotion, reciprocity edge, consumer-signature change, or component promotion is allowed.

Return exactly one verdict: `PASS-BOUNDED-BUILD`, `REVISE-MECHANICAL`, `REVISE-SUBSTANTIVE`,
`OBSTRUCTION`, or `NO-RESULT`. A PASS closes only the U1/U2 build-review stage; U3--U6 and the source
gate remain open.
