INDEPENDENT OPUS 4.8 BUILD REVIEW — P-ADIC-HODGE TIER-1 WEIGHT BOUNDARY

Difficulty 10 build review. Review the current repository delta read-only. Do not edit Lean,
control, graph, review, or task files.

The bounded built unit is:

- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`
- the import in `FLTMethodology.lean`
- `methodology/review/flt-completion/padic-hodge/stage-4-opus48-synthesis.md`
- `methodology/review/flt-completion/padic-hodge/stage-5-gpt56xhigh-review.md`
- `methodology/review/flt-completion/padic-hodge/stage-6-pinned-library-gap-audit.md`

Independently verify:

1. weights are indexed by global embeddings of the base number field, not the coefficient field;
2. `InFontaineLaffailleInterval` has one shared global base and the correct upper endpoint;
3. `EllUnramifiedInIntegers` uses the exact Mathlib unramifiedness predicate;
4. `GaloisRepDual` is a continuous contragredient representation with the inverse in the correct
   place and no silently missing topology hypothesis;
5. the two guards genuinely prove the `2 < ℓ` interval threshold and rejection of repeated weights;
6. targeted and umbrella builds pass and each of the seven public data declarations and two guards
   audits exactly to `[propext, Classical.choice, Quot.sound]`;
7. no `sorry`, `axiom`, `IsCrystallineAt`, Hodge--Tate extraction, or hidden historical/provider
   assumption was introduced;
8. the pinned-library audit is reproducible and does not mistake unrelated crystalline-cohomology
   material for p-adic-Hodge representation theory;
9. the full `FLT-MLT-PADIC-HODGE` obligation remains a definition gap with G1/G2/G4/G5/G6/G7 open;
10. the candidate provider decomposition is only a proposal and has not silently mutated the graph.

Run read-only targeted and umbrella builds and temporary `#print axioms` audits. Return `PASS` or
`REVISE`, with exact findings and the first remaining mathematical provider. Do not promote the full
p-adic-Hodge obligation. Lean's kernel/build output remains authoritative.
