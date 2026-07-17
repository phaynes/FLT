OPUS 4.8 BOUNDED BUILD — MODULARITY-LIFTING REVIEWED VOCABULARY SLICE

Work at difficulty 10 in the current repository. Implement only the independently reviewed,
definitions-only slice. Do not prove any open provider theorem, edit the proof graph/control rows,
register an axiom, alter existing FLT games or source contracts, or touch files outside this repo.

Read stages 4, 6, 7, 8, and 9 under
`methodology/review/flt-completion/modularity-lifting/`.

Required production:

1. Create `FLTMethodology/Probes/ResidualAbsoluteVocabulary.lean` containing exactly the three
   reviewed definitions in namespace `FLTMethodology.Taylor2018`:
   `IsAbsolutelyIrreducibleInResidualClosure`,
   `IsCyclotomicAbsolutelyIrreducibleInResidualClosure`, and
   `ClosureImpliesClassAbsIrred`.
   Include `Mathlib.NumberTheory.Cyclotomic.Basic` and use the exact universe pin
   `.{max uK uk uW, uK, uk, uW}`.
2. Create `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean` containing exactly the five
   frozen Stage-4 definitions: `SelectedGoodRepository`,
   `HasGenericTameRankOneQuotient`, `HasFlatDescentAboveEll`, `CyclotomicDegreeBound`, and
   `ComplexEmbeddingData`.
3. Add both imports to `FLTMethodology.lean` in leaf-alphabetical order.

Do not include `SourceHypotheses`, `SourceContract`, `CoefficientData`, bridge proofs, an example
applying `cyclic_base_change`, `sorry`, `axiom`, `admit`, `unsafe`, or `native_decide`.

Run targeted builds and `lake build FLTMethodology`. Create a temporary audit outside the repository
and `#print axioms` all eight declarations. Every declaration must report exactly
`[propext, Classical.choice, Quot.sound]`; fail closed otherwise. Return exactly one of
`BUILT-BOUNDED-SLICE`, `REVISE`, or `OBSTRUCTION`, with the changed files, build results, and axiom
output. The implication named by `ClosureImpliesClassAbsIrred` remains an open provider proposition,
not a proved theorem.
