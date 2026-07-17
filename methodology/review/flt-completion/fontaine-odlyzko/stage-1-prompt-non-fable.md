INDEPENDENT STAGE-1 DESIGN — FLT-FONTAINE-ODLYZKO

Repository: `/Volumes/second-store/devel/proof-forks/FLT`
Branch: `methodology/varro-proof-program-20260716`
Work-order start SHA: `827eb96`
Pipeline: `tri-design-synthesis-build`, Stage 1 only

## Authority and scope

Act as an independent mathematical and Lean designer. This is a fresh one-shot context. Read the
repository directly, but make no edits, create no files, run no mutating command, and do not attempt
the proof. Do not rely on the other Stage-1 designers. The repository may contain concurrent review
evidence; ignore every other model's Stage-1 output so this design remains independent.

Design only `FLT-FONTAINE-ODLYZKO`, the proposed core theorem
`FLT.HardlyRamified.modThree_classification_core`. Its consumer is
`GaloisRepresentation.IsHardlyRamified.mod_three`; do not quietly broaden the component to later
3-adic lifting, compatible families, or the final FLT theorem. The current graph classifies this as
a produced T2 component. Therefore distinguish exactly what must be produced kernel-cleanly from
any genuinely historical named numerical/discriminant input that may remain in the theorem's axiom
closure. Do not hide the classification itself behind a renamed assumption.

## Mandatory repository inspection

Inspect at least:

- `methodology/control/proof-obligations.ndjson`, rows `FLT-FONTAINE-ODLYZKO`, `FLT-MOD3`, and
  `FLT-HR-DEF`;
- `methodology/control/source-design.ndjson`, component `fontaine-odlyzko`;
- `methodology/SOURCE-REGISTER.md`, especially `SRC-003` and `SRC-007`;
- `methodology/LIBRARY-SURVEY.md`, `CURRENT-COMPONENT-INVENTORY.md`, `TRACEABILITY.md`, and the
  relevant source/evidence/review files found by search;
- `FLT/GaloisRepresentation/HardlyRamified/Defs.lean` and `ModThree.lean`;
- `FLT/Assumptions/Odlyzko.lean` and `FLT/Assumptions/README.md`;
- all actual imported or plausible finite-group, PGL2, number-field, discriminant, ramification,
  finite-flat, and linear-representation APIs in this pinned tree and Mathlib checkout.

Locate the exact present theorem types and every direct consumer. Do not infer availability from a
module name: use repository search and, where useful, read-only `#check`/temporary probes outside the
repository. Identify whether the current `Odlyzko_statement` is sufficient, too strong, too weak,
or incorrectly oriented for the planned contradiction.

## Required design analysis

Provide all of the following:

1. Exact consumer/source analysis. Quote the exact current Lean consumer signature and decompose its
   hypotheses and conclusion. Give exact primary-source locators for every nontrivial mathematical
   implication; label any locator not actually present in the repository as unresolved.
2. A complete mathematical case graph from a hypothetical irreducible two-dimensional mod-3 hardly
   ramified representation to the required invariant one-dimensional quotient. Include coefficient
   field reduction, projective image classification, cut-out fields, archimedean signature,
   ramification/discriminant estimates, the numerical contradiction, and the final linear-algebra
   orientation. State which cases genuinely need separate treatment.
3. Exact proposed Lean signatures, in dependency order, for the smallest source-faithful route.
   Distinguish existing declarations, repaired interfaces, new produced lemmas, and exact named
   historical numerical assumptions. Avoid pseudo-Lean: bind universes, typeclasses, parameters,
   representations, fields, primes, and output orientation sufficiently for elaboration.
4. A transitively reduced dependency graph and an explicit join theorem that exports the exact
   `mod_three` conclusion without changing it.
5. Library matches. For every proposed node, identify the closest exact pinned declaration or state
   `NONE FOUND`; do not use aspirational module names as evidence.
6. Counterexamples and hostile checks. Test at least: non-prime finite coefficient fields;
   `Algebra Z_[3] k` versus actual characteristic 3; reducible but non-split representations;
   invariant subspace versus invariant quotient orientation; projective versus linear image;
   real versus totally complex cut-out fields; discriminant bounds insufficient to force the
   claimed group case; and any accidental use of the desired classification as an assumption.
7. The first buildable kernel-clean slice, with exact file/module placement, imported dependencies,
   theorem signatures, and its completion audit. Prefer a small slice that retires a real graph edge.
8. A stop-loss gate: the earliest statement/source/library condition that would make this design
   unsound or require decomposition/re-authorisation. Do not propose implementation past that gate.
9. A component Definition-of-Ready checklist for source exactness, hypothesis translation, proof
   outline, sublemma graph, counterexample review, library matches, and elaborated signatures.

## Output contract

Return exactly these sections:

1. `VERDICT` — one of `DESIGN-VIABLE`, `DECOMPOSE-FIRST`, or `OBSTRUCTION`, with one paragraph.
2. `CURRENT EXACT BOUNDARY`
3. `SOURCE AND CONSUMER AUDIT`
4. `DEPENDENCY GRAPH`
5. `PROPOSED LEAN SIGNATURES`
6. `LIBRARY MATCHES`
7. `COUNTEREXAMPLES AND FAILURE MODES`
8. `FIRST BUILDABLE SLICE`
9. `STOP-LOSS GATE`
10. `DEFINITION OF READY`
11. `OPEN QUESTIONS FOR SYNTHESIS`

Be explicit about uncertainty. A source citation, scaffold, `sorry` declaration, or axiom is not a
proof. Do not describe the component as ready unless the proposed signatures and source translation
are precise enough for a subsequent independent synthesis and kernel probe.
