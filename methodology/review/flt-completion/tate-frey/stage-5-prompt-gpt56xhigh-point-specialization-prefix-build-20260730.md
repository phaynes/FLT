# Stage 5 — GPT-5.6 xhigh point-specialization prefix build

Work only in the supplied isolated FLT worktree and on its current branch. This is the only active
proof-mutating task.

## Mission

Advance the unchanged theorem `WeierstrassCurve.torsion_unramified_of_good_reduction` by proving
the largest honest kernel-green prefix of its point-specialization package, starting with integral
unit-coordinate normalization and projective residue reduction.

Read:

- `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`;
- `FLTMethodology/Probes/GoodReductionBoundary.lean`;
- the Stage 3 prompt and response;
- `stage-4-opus48-point-specialization-design-response-20260730.md`;
- the actual pinned Mathlib projective-point, valuation-subring, residue-field, and elliptic-reduction
  APIs;
- the vendored Hasse–Weil division-polynomial slice only where it genuinely matches the target.

## First executable tranche

Prove reusable declarations, with exact types chosen from the pinned APIs, for as much as can be
completed in this order:

1. a nonzero `Fin 3` vector over the fraction field of a valuation subring can be scaled to a vector
   whose coordinates lie in the valuation subring and with at least one unit coordinate;
2. residue reduction of such a vector is nonzero;
3. the construction respects unit scaling and therefore defines a projective point class;
4. for the integral Weierstrass model, the reduced representative satisfies the reduced equation and
   is nonsingular under good reduction;
5. assemble a total specialization map on `(E⁄ksep).Point`;
6. prove inertia invariance using the existing `inertia_residue_smul_eq`.

Prefer small generic normalization lemmas when they make the elliptic construction tractable. Do
not over-generalize beyond what this target consumes.

## Hard prohibitions

- Do not introduce `sorry`, `admit`, an axiom, an opaque hypothesis, or a target-equivalent contract.
- Do not replace a proof with a definition whose field is the missing theorem.
- Do not edit the obligation graph, claim the target closed, or claim FLT progress beyond declarations
  that independently pass the kernel audit.
- Do not use cached AINTLIB theorems whose axiom closure includes admissions.
- Do not commit, push, or mutate Helios task state; the controller will validate and preserve work.

The target itself may be changed only if every required provider is genuinely proved. Otherwise
leave its existing `sorry` untouched.

## Adaptive execution

Iterate against Lean. If a proposed abstraction is not supported by the pinned API, reduce the
tranche to the nearest useful real lemma rather than fabricating an interface. Search the local API
before proving infrastructure from scratch. Stop before an unbounded scheme-theoretic detour.

If normalization succeeds but the curve-specific map does not, return the kernel-green normalization
library as the bounded result and name the exact next type mismatch. If no real declaration can be
completed, leave the source unchanged and return a source-grounded blocked diagnosis.

## Required validation and report

Run, at minimum:

1. direct elaboration of every changed Lean file;
2. the narrow good-reduction target/probe build;
3. `lake -H build FLT FLTMethodology`;
4. `#print axioms` for every new or changed claimed declaration;
5. `git diff --check` and a scan proving no new prohibited token was added.

Return one leading verdict:

- `KERNEL-GREEN-PREFIX`;
- `TARGET-KERNEL-GREEN`;
- `NO-REAL-PROGRESS`.

List exact declarations proved, files changed, build job counts, axiom closures, remaining boundary,
model/session/timing/token evidence, and whether the original target still contains `sorryAx`.

