# Stage 5 prompt — GPT-5.6 xhigh independent review of modularity-lifting synthesis

Difficulty 10. Act as the independent mathematical, source, and Lean reviewer. Work read-only: do
not edit repository files, task state, graph rows, source registers, or Lean sources. Temporary Lean
probes outside the repository are allowed.

Read in full:

- `methodology/review/flt-completion/modularity-lifting/stage-1-opus48-primary.md`;
- `methodology/review/flt-completion/modularity-lifting/stage-2-gpt56xhigh-review.md`;
- `methodology/review/flt-completion/modularity-lifting/stage-3-fable5-diversity.md`;
- `methodology/review/flt-completion/modularity-lifting/stage-4-opus48-synthesis.md`;
- the current coefficient and p-adic-Hodge reviewed artifacts and exact live consumers cited there.

Adjudicate whether the Stage-4 synthesis actually repairs the Stage-2 substantive defects. In
particular verify:

1. the five proposed `SelectedGoodRepositoryBoundary` declarations have exact elaborating Lean
   signatures at the current pin and are the smallest honest first buildable unit;
2. their declaration axiom surfaces are exactly `[propext, Classical.choice, Quot.sound]` and no
   declaration term-depends on the sorried `cyclic_base_change` theorem;
3. generic-fibre tame quotient, integral flat descent, and `BlueprintSGood.traceOnJ` remain distinct,
   with any relationship left as an explicit future bridge;
4. one explicit coefficient owner and one residual model really own both source residual agreement
   and cyclotomic-restriction irreducibility;
5. `{-1,0}` belongs to the repository representation and `{0,1}` only to its dual under the live
   determinant convention;
6. cyclotomic degree, complex embedding, support away from ell, p-adic-Hodge, and RACAR ownership are
   complete and do not hide a target theorem or reverse a dependency;
7. `FLT-MLT-SOURCE` remains gated on coefficients, p-adic-Hodge Tier-2, and RACAR rather than being
   promoted from an elaborating data shell;
8. the proposed probe import, namespaces, universes, and typeclass assumptions reproduce in a
   temporary file, including all five `#print axioms` audits;
9. every claimed source-to-repository separation matches Taylor 2018 Theorem 2.1.1 and the live
   `GaloisRep.IsAutomorphicOfLevel` / `cyclic_base_change` consumer shapes;
10. the dependency graph and stop-loss conditions are sufficient to prevent `sorryAx`, generic
    `Prop` placeholders, or an unreviewed public axiom entering the build.

Return exactly one of `PASS`, `REVISE-MECHANICAL`, `REVISE-SUBSTANTIVE`, `REFUTED`, or `NO-RESULT`.
Give exact findings, temporary-probe results, declaration axiom audits, the smallest authorized next
build unit if PASS, and the first expected residual Lean goal. A PASS may authorize only the bounded
five-unit probe build; it cannot promote the full source theorem or SelectedGood obligation.
