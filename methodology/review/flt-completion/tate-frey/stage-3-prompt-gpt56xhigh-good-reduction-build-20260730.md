# Stage 3 — bounded good-reduction specialization build

You are the sole Lean-mutating builder for one governed FLT leaf.

## Frozen scope

- repository: `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`
- base: `1450031e86f8f2baf354c35f1c77c0bff09b279b`
- branch: `codex/ca-flt-good-reduction-specialization-20260730`
- Helios task: `task:ca-flt-good-reduction-specialization-20260730`
- target declaration:
  `WeierstrassCurve.torsion_unramified_of_good_reduction`
- target file: `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`
- owning obligation: `FLT-TATE-UNRAMIFIED`

No other proof-mutating agent is active. Do not create subagents. Do not commit, push, mutate Helios
tasks, or promote any obligation; the controller owns those actions after independent review.

## Objective

Replace the target's direct `sorry` with a genuine Lean proof having exactly the standard axiom
trio `[propext, Classical.choice, Quot.sound]`. You may add narrowly reusable production support
declarations and one dedicated methodology probe when needed, but introduce no `sorry`, `sorryAx`,
custom axiom, `knownin1980s`, target-equivalent hypothesis, or unrelated theorem. Preserve the
public target statement unless you prove that it is malformed; in that case stop with a precise
counterexample or type-level obstruction instead of weakening it silently.

## Required grounding

Read before editing:

- `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`;
- `FLTMethodology/Probes/GoodReductionBoundary.lean`;
- `methodology/evidence/probes/FLT-TATE-UNRAMIFIED-DEPENDENCY-SLICE.md`;
- `methodology/evidence/probes/FLT-TATE-FLAT-CONSUMER-SLICE.md`;
- `methodology/review/flt-completion/tate-frey/implementation-handoff-20260719.md`;
- `methodology/review/flt-completion/tate-frey/stage-1-opus48-primary.md`;
- the exact pinned Mathlib reduction, projective-point, valuation-subring, decomposition-group,
  inertia, torsion, and finite-étale APIs implicated by the statement.

Literature context is available out of band at:

- `/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd`;
- `/Volumes/second-store/devel/proof-forks/FLT-primary-literature-enrichment-20260719/build/literature-enrichment/cache/Joseph H. Silverman - Advanced Topics in the Arithmetic of Elliptic Curves (1994) [978-1-4612-0851-8].pdf`.

These sources explain the classical good-reduction/unramified-torsion route, but a citation is not
a Lean provider. Treat the existing `PointSpecializationContract` as a specification probe only,
never as an assumption. Search the actual pinned library exhaustively before designing missing
infrastructure.

## Execution discipline

1. Reproduce the target and its direct dependencies at the exact base.
2. Enumerate the smallest missing mathematical/Lean providers and test candidate APIs in disposable
   `/tmp` probes before production edits.
3. Prefer existing Mathlib declarations and objective reduction/injectivity arguments. If the
   projective reduction/Neron-model infrastructure is absent, identify the smallest honest reusable
   construction rather than postulating the full classical theorem.
4. Iterate against Lean after every small step. Keep edits inside the target/support closure.
5. Run prohibited-token searches over every added or modified Lean file.
6. Run direct elaboration, the narrow build, and `lake -H build FLT FLTMethodology` if a candidate
   closes.
7. Audit the target and every new exported declaration with `#print axioms`.

## Stop-loss and result contract

Return exactly one leading verdict:

- `KERNEL-GREEN-GOOD-REDUCTION` only if the unchanged target is proved, builds pass, and every new
  declaration has exactly the standard trio;
- `BOUNDED-PREFIX-GREEN` only if you prove useful prerequisite declarations but the target remains
  open—name the exact remaining theorem and do not claim obligation closure;
- `STATEMENT-OR-LIBRARY-BLOCKED` if the target cannot honestly be completed in this tranche—give the
  smallest exact missing provider, why current APIs cannot supply it, and the strongest tested next
  step.

Report changed files, commands and job counts, exact axiom output, remaining admissions in the
closure, transcript/session telemetry if available, and the precise graph effect. Do not claim that
`FLT-TATE-UNRAMIFIED`, Tate/Frey, any consumer, or FLT is complete unless the evidence actually
establishes that separate boundary.
