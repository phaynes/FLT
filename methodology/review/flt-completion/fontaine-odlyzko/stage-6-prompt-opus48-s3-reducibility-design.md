OPUS 4.8 PRIMARY DESIGN — FONTAINE--ODLYZKO S3 REDUCIBILITY BRIDGE

Act as the primary mathematical and Lean designer for the next bounded node of
`FLT-FONTAINE-ODLYZKO` at difficulty 10. Work read-only. Do not edit repository files or task state.

The characteristic-three leaf has been built and independently reviewed. The full component remains
open. Design only S3: the exact arbitrary-finite-coefficient-field linear-algebra bridge from
`¬ ρ.IsIrreducible` for a rank-two Galois representation to a proper stable rank-one submodule and a
correctly oriented one-dimensional quotient. Do not claim that the quotient character is trivial;
that belongs to later local/global input.

Read at least:

- `methodology/review/flt-completion/fontaine-odlyzko/stage-3-gpt56xhigh-review.md`
- `methodology/review/flt-completion/fontaine-odlyzko/stage-5-gpt56xhigh-charp-build-review.md`
- `FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`
- `FLT/Deformations/RepresentationTheory/GaloisRep.lean`
- `FLT/Slop/RepresentationTheory/OddAbsIrredSlop.lean`
- `FLTMethodology/Probes/MazurSourceBoundary.lean`
- Mathlib representation/subrepresentation, quotient, finite-dimensional, and character APIs.

Required work:

1. State the smallest mathematically true S3 output. Prefer a stable subrepresentation `W` with
   `W ≠ ⊥`, `W ≠ ⊤`, `finrank k W = 1`, `finrank k (V ⧸ W) = 1`, the canonical surjective quotient,
   and its equivariance under `ρ`.
2. Determine whether an actual multiplicative quotient character
   `χ : Γ ℚ →* k` and a linear equivalence `V ⧸ W ≃ₗ[k] k` can be constructed without arbitrary
   basis choices breaking multiplicativity. If yes, give and probe the exact signature; if not,
   retain the quotient representation as the stable interface and explain the later character bridge.
3. Prove or probe the extraction from `¬ ρ.IsIrreducible` using the exact current definition. Exclude
   the spurious `V = 0` branch from `Module.rank k V = 2` explicitly.
4. Confirm all rank and quotient formulas under the repository's `Module.Finite`/`Module.Free`
   hypotheses and general universe levels.
5. Run temporary Lean probes outside the repository. `#print axioms` must return exactly
   `[propext, Classical.choice, Quot.sound]` for every proposed bankable declaration.
6. Return the dependency-ordered exact declarations, temporary probe results, the smallest safe
   production slice, and the first residual Lean goal.

Hostile checks:

- do not reverse the required final quotient orientation;
- do not infer a trivial quotient merely from reducibility;
- do not use undefined placeholders such as `stable`, `charOfSub`, or paper notation;
- do not import or consume `sorryAx`, `knownin1980s`, `Odlyzko_statement`, N1, or N2;
- do not weaken the finite arbitrary field `k` to `ZMod 3` unless you prove transport back;
- distinguish a structure/definition that merely packages hypotheses from a theorem that derives
  them.

Verdict exactly one of `DESIGN-VIABLE`, `REVISE`, or `OBSTRUCTION`.
