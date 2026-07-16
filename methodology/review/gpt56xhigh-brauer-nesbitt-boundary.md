# GPT-5.6 xhigh review: Brauer--Nesbitt boundary

Candidate: `d414ef1`.

Model: `gpt-5.6-sol`, reasoning `xhigh`. Mode: fresh, read-only, bounded hostile source and
implementability review. Approximate elapsed wall time: thirteen minutes. The bridge did not expose
an exact elapsed field.

Verdict: **REVISE BRAUER-NESBITT BOUNDARY**.

The reviewer independently reproduced the build, the standard-trio axiom audits, the exact scope
of the finite counterexample, and the implication
`GroupContract -> SemisimplifiedResidualModelsUnique`.

Load-bearing findings:

- `GroupContract` is true as stated and already has the needed finite-dimensionality through
  `Module.Finite`; no perfectness, algebraic closure, finite group, continuity, or finite-image
  hypothesis should be added.
- The documented arbitrary-field route is incomplete because finite-dimensional semisimple
  algebras over imperfect fields need not have the asserted finite separable splitting field.
- `SimpleCharactersLinearIndependentContract` is correctly scoped and absent from the pinned
  library, but it is an algebraically closed specialization terminal rather than the first complete
  arbitrary-field terminal.
- The rank-two odd-characteristic contract is true, but the frozen consumer lacks its algebraic
  closure, dimension, and characteristic hypotheses.
- The counterexample proves that the one-sided dimension bound is insufficient; it does not alone
  prove independent necessity of the strict characteristic bound.

Required action: keep the full graph node open, replace the source route with a source-checked
finite-dimensional joint-image/spanning-set proof, use `sufficient` rather than `exactly
sufficient`, and do not schedule the rank-two shortcut without a reviewed specialized consumer.
No repository file was modified by the reviewer.
