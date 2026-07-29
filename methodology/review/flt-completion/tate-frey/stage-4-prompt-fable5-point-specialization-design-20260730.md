# Stage 4 — Fable 5 point-specialization design

Perform a read-only, source-grounded design of the exact remaining provider for
`WeierstrassCurve.torsion_unramified_of_good_reduction`.

## Frozen state

- repository: `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`
- candidate prefix: `a4fe177`
- task: `task:ca-flt-good-reduction-specialization-20260730`
- owning obligation: `FLT-TATE-UNRAMIFIED`

The GPT-5.6 xhigh Stage 3 run proved `ValuationSubring.baseRingHom`, `coe_baseRingHom`, and
`isLocalHom_baseRingHom`. It did not alter the target, which still has its original `sorry`.

Read the target file, `FLTMethodology/Probes/GoodReductionBoundary.lean`, the Stage 3 prompt and
response, the Tate/Frey handoff and prior designs, and the actual pinned Mathlib and AINTLIB trees.
Use the converted Silverman material and inspected PDF named in the Stage 3 prompt as mathematical
context. A citation is not a Lean provider.

## Design question

Give the smallest honest, dependency-ordered Lean construction of the geometric tail:

1. specialization of a separable-closure elliptic point through a valuation subring to the reduced
   projective curve;
2. inertia invariance;
3. injectivity on `n`-torsion when `n` is nonzero in the residue field;
4. composition with `torsion_fixed_of_invariant_injective` to close the unchanged target.

Audit at least these competing routes against actual declarations and types:

- normalized integral projective coordinates plus residue reduction;
- a direct division-polynomial/coprimality proof using the already proved
  `isCoprime_Φ_ΨSq`;
- generic properness/valuative-criterion and finite-etale infrastructure;
- any importable AINTLIB torsion-unramified-fibre theorem plus an explicit bridge to
  `WeierstrassCurve`.

Reject any design that assumes the target, injectivity, the Neron model, or a target-equivalent
specialization contract. State whether the current target is mathematically and type-theoretically
sound at its full generality. If a large foundational layer is unavoidable, recursively decompose it
into independently buildable declarations, with exact proposed Lean signatures, imports, objective
oracles, counterexamples, and a stop-loss boundary. Identify the first executable tranche that has
the highest probability of kernel-green completion, not merely the shortest prose description.

## Result contract

Return exactly one leading verdict:

- `IMPLEMENTABLE-NOW` with an exact first build tranche and terminal dependency graph;
- `IMPLEMENTABLE-AFTER-NAMED-PREFIX` with the smallest exact prefix and why it is sufficient;
- `STATEMENT-REPAIR-REQUIRED` with a concrete defect;
- `FOUNDATIONAL-LIBRARY-BLOCKED` only after demonstrating that no honest bounded construction can
  advance the provider.

Do not edit, commit, push, mutate tasks or graph state, introduce axioms, or claim proof progress.
