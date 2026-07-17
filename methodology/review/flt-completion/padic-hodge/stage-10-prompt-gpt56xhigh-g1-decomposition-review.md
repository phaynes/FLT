GPT-5.6 XHIGH INDEPENDENT REVIEW — P-ADIC-HODGE G1 DECOMPOSE-FIRST DESIGN

Work read-only at difficulty 10. Review the Opus G1 design against the pinned library and the exact
Taylor source boundary. Do not edit repository files, task state, or graph rows.

Read:

- `methodology/review/flt-completion/padic-hodge/stage-6-pinned-library-gap-audit.md`;
- `methodology/review/flt-completion/padic-hodge/stage-9-opus48-g1-crystalline-design.md`;
- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`;
- every pinned period-ring, tensor-action, invariant-submodule, local-place, and completion API cited.

Independently verify:

1. whether `A_cris`, `B_cris`, `D_cris`, or a crystalline Galois-representation predicate is
   truly absent from the pin;
2. whether the proposed `IsPlaceAbove`, parameterized period module, diagonal action, invariant
   module, and `IsCrystallineRel` signatures are mathematically honest and non-vacuous;
3. whether the proposed first slice hides any of the desired crystalline theorem as structure data;
4. the exact dependency order from diagonal tensor action through A_cris/B_cris and comparison;
5. the smallest standard-trio production unit and its first residual Lean goal.

Run disposable signature probes where feasible. Return exactly one of `PASS-DECOMPOSE-FIRST`,
`REVISE`, or `OBSTRUCTION`. PASS authorizes only the reviewed parameterized infrastructure, not
an `IsCrystallineAt` theorem and not promotion of the full p-adic-Hodge obligation.
