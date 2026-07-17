OPUS 4.8 PRIMARY DESIGN — P-ADIC-HODGE G1 CRYSTALLINE REPRESENTATION BOUNDARY

Work read-only at difficulty 10. Design only the first open mathematical provider beneath the
reviewed p-adic-Hodge Tier-1 vocabulary: G1, an exact `GaloisRep.IsCrystallineAt` predicate backed by
a genuine period-ring `D_cris` construction. Do not edit repository files, task state, or the graph.

Read:

- `methodology/review/flt-completion/padic-hodge/stage-4-opus48-synthesis.md`
- `methodology/review/flt-completion/padic-hodge/stage-5-gpt56xhigh-review.md`
- `methodology/review/flt-completion/padic-hodge/stage-6-pinned-library-gap-audit.md`
- `methodology/review/flt-completion/padic-hodge/stage-7-opus48-build-review.md`
- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`
- the pinned Mathlib local-field, valuation, completion, tensor-product, invariants, and Galois APIs.

Required work:

1. Reconfirm whether the pinned dependency tree has any reusable p-adic period-ring or crystalline
   representation implementation. Distinguish crystalline cohomology from crystalline Galois
   representations.
2. State the smallest mathematically correct definitions needed for `B_cris`, its topology and
   actions, `D_cris(V)`, and the dimension equality defining crystallinity. Expose every prerequisite
   rather than hiding period-ring mathematics in a Prop field.
3. Give exact universe-polymorphic Lean signatures at the repository's current `GaloisRep` and local
   place types. Determine the minimum coefficient field and completion data required.
4. Produce a dependency graph separating routine Lean infrastructure from genuine mathematical
   provider theorems, with source boundaries and estimated difficulty for each node.
5. Run read-only `#check` probes for every cited existing declaration and temporary signature probes
   where feasible. No proposed bankable declaration may inherit `sorryAx`, `knownin1980s`, or a
   custom axiom.
6. Decide whether a bounded first production slice exists now. If the full predicate cannot be
   responsibly defined against the pin, identify the smallest prior component to build first and its
   exact interface.

Hostile checks:

- do not use an abstract `IsCrystalline` field whose only content is the desired theorem;
- do not confuse global embeddings with local places above ell;
- do not assume finite-flat implies crystalline in G1; that is the separate G4 provider;
- do not claim Hodge--Tate weights or Fontaine--Laffaille bounds from crystallinity alone;
- do not rely on a newer Mathlib API unless you identify the exact reusable declarations and a
  controlled upgrade path;
- preserve the standard-trio target for all produced infrastructure.

Return exactly one of `DESIGN-VIABLE`, `DECOMPOSE-FIRST`, or `OBSTRUCTION`. Give exact proposed Lean
signatures, source and library evidence, the smallest safe build unit, and its first residual goal.
