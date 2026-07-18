# GPT-5.6 xhigh independent review — closure-to-class absolute irreducibility

Act as an independent hostile mathematical and Lean reviewer at difficulty 10. Review the exact
commit named by the controller when launching this prompt. Work read-only in
`/Volumes/second-store/devel/proof-forks/FLT`; temporary Lean probes outside the repository and
`lake build` are allowed. Do not edit source, control rows, review packets, task state, or git.

Read in full:

- `FLTMethodology/Probes/ResidualAbsoluteVocabulary.lean`;
- `FLT/Slop/RepresentationTheory/OddAbsIrredSlop.lean`;
- `FLT/Deformations/RepresentationTheory/Irreducible.lean`;
- `methodology/review/flt-completion/modularity-lifting/stage-14-controller-closure-bridge-build.md`;
- the exact `FLT-ABSIRRED-VOCAB` obligation and both consumer edges.

Independently verify:

1. Burnside/Schur is used with all required finite-dimensional, simplicity, and algebraically closed
   hypotheses and does not smuggle absolute irreducibility into an instance.
2. The tensor-product algebra map in the descent lemma really has a range containing every extended
   representation generator. Check the range/top orientation and every finrank equality.
3. Full image-algebra density over the base field is sufficient for irreducibility after every field
   extension; check nontriviality of each tensor module and the universe pinned by the class.
4. Conversion between `Representation.baseChange` and `Slop.OddRep.baseChange` is definitional at the
   exact types used, with no hidden topology or scalar-tower assumption.
5. Run the targeted module build and temporary-file axiom audits for all three new declarations.
   Require exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`, custom axiom,
   `knownin1980s`, `admit`, `unsafe`, or `native_decide` on their dependency paths.
6. Confirm the theorem proves exactly `ClosureImpliesClassAbsIrred`; it must not be credited with
   either concrete cyclotomic residual-image application or the Taylor source theorem.

Return exactly one verdict: `PASS-BRIDGE`, `REVISE-MECHANICAL`, `REVISE-SUBSTANTIVE`,
`OBSTRUCTION`, or `NO-RESULT`. A pass authorizes an Opus final build seal before the obligation is
marked proved.
