# Independent executable review — FLT tame-residue completion candidate

Review this candidate adversarially and read-only:

- repository: `/Volumes/second-store/devel/proof-forks/FLT-tame-residue-completion-20260730`
- frozen candidate commit: `b78328972fb5d2072fb9959c7afcda0ff88e17b0`
- obligation: `FLT-TAME-RESIDUE`
- target stage: `T1`

The producing agent was GPT-5.6 xhigh. You are the independent reviewer. Treat its response, the
controller evidence packet, the earlier designs, and every source assertion as claims to test.

## Required inspection

Read at least:

- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`
- `FLT/Deformations/RepresentationTheory/FixedFieldUniformizer.lean`
- `FLT/Mathlib/RingTheory/RootsOfUnity/ResidueField.lean`
- `FLTMethodology/Probes/TameResidueBoundary.lean`
- `FLTMethodology/Probes/FixedFieldUniformizerBoundary.lean`
- `FLT.lean` and `FLTMethodology.lean`
- the exact `FLT-TAME-RESIDUE` row in `methodology/control/proof-obligations.ndjson`
- Stages 23–27 under `methodology/review/flt-completion/class-field/`
- `methodology/evidence/probes/FLT-TAME-RESIDUE-COMPLETION-20260730.md`

Verify that the frozen candidate is an ancestor of HEAD and that any later changes are review-only.
Do not trust the current worktree if it is dirty.

## Mandatory executable checks

Run, without modifying tracked files:

```bash
git status --short
git diff --check 4642bcd..b78328972fb5d2072fb9959c7afcda0ff88e17b0
lake env lean FLT/Deformations/RepresentationTheory/FixedFieldUniformizer.lean
lake env lean FLTMethodology/Probes/FixedFieldUniformizerBoundary.lean
lake build FLT.Deformations.RepresentationTheory.FixedFieldUniformizer FLTMethodology.Probes.FixedFieldUniformizerBoundary
lake build FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup FLTMethodology.Probes.TameResidueBoundary
lake build FLT FLTMethodology
```

Independently report the `#print axioms` result for every new declaration. Check for `sorry`,
`sorryAx`, `admit`, `native_decide`, custom axioms, hidden provider assumptions, and accidental use
of unrelated admitted methodology. Do not count standard `[propext, Classical.choice, Quot.sound]`
as a defect.

## Mathematical review obligations

Check each point explicitly:

1. normality of local inertia and the use of the infinite Galois correspondence;
2. correctness and non-circularity of the finite integral-closure DVR/fraction-ring/Galois pack;
3. both inclusions in the finite/infinite inertia restriction equality;
4. the residue-action correction, including that the quotient action is over the finite residue
   field, the profinite stabilizer theorem applies to the actual carriers, and `sigma * rho^-1`
   has both the required residue action and the same finite restriction;
5. the passage from trivial finite inertia to ramification index one;
6. maximal-ideal generation, irreducibility, integer-power/unit factorization, and all algebra-map
   and `zpow` coercions;
7. containment of every fixed-field element in a finite Galois intermediate field still lying in
   the inertia fixed field;
8. exact satisfaction of `FixedFieldUniformizerDecomposition` and the final unconditional kernel
   theorem without weakening either statement;
9. import direction and downstream consumer compatibility;
10. whether the retained Neukirch locator review supports the mathematics, while separately noting
    that this worktree does not yet contain a hash-verified local primary-source copy or `SRC-026`.

Try to construct a counterexample or identify an instance/coercion ambiguity that Lean elaboration
would not expose. Do not infer source verification merely from a citation.

## Verdict contract

Return exactly one leading verdict:

- `PASS-TAME-RESIDUE-KERNEL` only if the exact theorem is mathematically sound, independently
  rebuilt, and standard-trio clean;
- `REVISE` with the smallest concrete defect and exact file/declaration;
- `NO-RESULT` only for an operational failure, kept distinct from a proof defect.

Then state the exact promotion scope and exclusions. In particular, adjudicate separately:

- kernel theorem/build completion;
- source-grounded status;
- the honest `FLT-TAME-RESIDUE` graph state after review;
- downstream consumer consequences;
- the fact that neither `FLT-CLASS-FIELD` nor FLT itself follows merely from this tranche.

Do not edit, commit, push, or update the graph.
