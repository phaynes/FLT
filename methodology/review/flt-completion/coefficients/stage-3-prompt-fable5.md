# Conditional Fable 5 diversity design — coefficients repair

Act as the independent Fable diversity designer for `FLT-MLT-COEFFICIENTS` at difficulty 10. Work read-only. Read:

- `stage-1-opus48-primary.md`
- `stage-2-gpt56xhigh-review.md`
- `FLTMethodology/Probes/MLTSourceBoundary.lean`
- the current coefficient, residual-representation, DVR, topology, tensor/base-change, and Brauer-Nesbitt APIs in the pinned repository and Mathlib.

The GPT review substantively refuted the Opus design: A1 is false as quantified, the W00 signatures do not elaborate, the ambient coefficient context is erased, U6 omits its claimed common-residual comparison, and A4 does not prove lattice independence. Do not patch these cosmetically.

Produce an independent repaired design that:

1. Gives exact elaborating Lean signatures for a data-only coefficient/lattice/residual bundle with all source parameters retained explicitly.
2. Separates existence of a stable lattice, construction of a continuous residual representation, comparison in a fixed common residual algebraic closure, semisimplification, and actual lattice independence.
3. States which units are definitions/probes buildable now and which are genuine T1 mathematical theorems with explicit owners and dependencies.
4. Provides counterexamples against overgeneralized rank or lattice-independence claims.
5. Preserves the Taylor 2018 source boundary and the frozen T1 axiom policy; no `sorry`, generic authority axiom, or T2 deferral of a T1 obligation.
6. Identifies the smallest exact next Lean probe and a dependency-ordered build graph.

Run temporary read-only Lean probes where needed. Return `DESIGN-VIABLE`, `DECOMPOSE-FIRST`, or `OBSTRUCTION`. Do not edit repository files, promote an obligation, or register an axiom.
