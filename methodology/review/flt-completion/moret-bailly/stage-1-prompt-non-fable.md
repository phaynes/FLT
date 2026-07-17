INDEPENDENT STAGE-1 DESIGN — FLT-MORET-BAILLY

Repository: `/Volumes/second-store/devel/proof-forks/FLT`
Branch: `methodology/varro-proof-program-20260716`
Work-order start SHA: `827eb96`
Pipeline: `tri-design-synthesis-build`, Stage 1 only

## Authority and scope

Act as an independent mathematical and Lean designer in a fresh one-shot context. Read the actual
repository but do not edit it, create files, run mutating commands, or attempt implementation. Do
not read or rely on any other Stage-1 model output: independence is required.

Design only the produced component `FLT-MORET-BAILLY`, proposed as
`FLT.PotentialModularity.moret_bailly_point`. Its interface must serve the actual downstream
auxiliary-curve and auxiliary-field consumers without absorbing those consumers' project-specific
mathematics. In particular, keep source-level Moret–Bailly hypotheses/conclusions separate from
even degree, Galois closure, total reality, quaternion splitting, residual/cyclotomic disjointness,
good reduction, and local unramifiedness unless the exact source theorem really includes them.
Do not replace the theorem by a generic existence axiom or assume independence of field conditions.

## Mandatory repository inspection

Inspect at least:

- `methodology/control/proof-obligations.ndjson`, rows `FLT-MORET-BAILLY`, `FLT-AUX-CURVE`,
  `FLT-AUX-LOCAL-FIELD`, and all their direct dependencies/consumers;
- `methodology/control/source-design.ndjson`, component `moret-bailly`;
- `methodology/SOURCE-REGISTER.md`, especially `SRC-011`, and exact source evidence present locally;
- `methodology/TRACEABILITY.md`, `MLT-SOURCE-CONTRACT.md`, `LIBRARY-SURVEY.md`,
  `CURRENT-COMPONENT-INVENTORY.md`, `RISK-REGISTER.md`;
- `methodology/evidence/sources/modularity-lifting-source-audit.md`,
  `methodology/review/gpt56xhigh-source-correction.md`, and the convergence review;
- all present potential-modularity, auxiliary-field, variety/scheme, local topology, number-field,
  disjointness, finite-extension, and rational-point APIs in FLT and the pinned Mathlib checkout.

Locate every exact downstream consumer rather than designing from blueprint prose. Use read-only
repository search and, if useful, temporary `#check` probes outside the repository. If the primary
source text needed to validate an exact hypothesis is not locally available, record that as a
source gate rather than hallucinating the theorem.

## Required design analysis

Provide all of the following:

1. Exact consumer inventory: every field/result downstream code needs, who owns it, and which subset
   should be supplied by the source theorem versus a project adapter. Include the corrected Taylor
   2018 distinction between unramifiedness and complete splitting.
2. Exact source theorem and locator. Translate the variety assumptions, smoothness/geometric
   integrality, finite places/local opens, non-emptiness, rational/global point, field extension,
   linear disjointness, and archimedean/totally-real conditions one by one. Mark any unverified
   condition.
3. A minimal two-layer interface architecture: (a) source-faithful Moret–Bailly theorem; (b) project
   adapter(s) for the actual auxiliary field/curve use. Explain why no project-specific conclusion
   leaks into the reusable source theorem.
4. Exact proposed Lean signatures in dependency order. Avoid pseudo-Lean: bind the base number
   field, extension, scheme/variety, finite set of places, local fields, open subsets, rational
   points, embeddings, disjointness extensions, and output witnesses sufficiently to elaborate in
   the pinned library. If current libraries cannot express the source statement, give the smallest
   prerequisite definitions and signatures first.
5. A transitively reduced dependency graph including local-open construction and the downstream
   adapters, with build gates made explicit.
6. Library matches for each proposed node. Name exact pinned declarations and types, or say
   `NONE FOUND`; distinguish topological openness from Zariski openness and points over completions
   from points over the global field.
7. Counterexamples/hostile cases: independent local witnesses that do not globalise; pairwise versus
   joint disjointness; splitting silently substituted for unramifiedness; Galois closure destroying
   local conditions; total reality/even degree asserted without construction; empty local opens;
   rational points over the wrong field; and circular use of the auxiliary-curve theorem.
8. The first buildable kernel-clean slice, including exact module/file placement, signatures,
   imports, and what graph edge it retires. Prefer elaborated data/contracts or a true adapter lemma,
   not a restatement of the desired conclusion.
9. A stop-loss gate at the first missing source fact, incompatible signature, or absent foundational
   API that would require redesign or operator authorisation.
10. A Definition-of-Ready checklist for source exactness, hypothesis translation, proof outline,
    sublemma graph, counterexample review, library matches, and elaborated signatures.

## Output contract

Return exactly these sections:

1. `VERDICT` — one of `DESIGN-VIABLE`, `INTERFACE-FIRST`, or `OBSTRUCTION`, with one paragraph.
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

Be hostile to accidental strengthening, weakened source hypotheses, and architecture that mixes
source theorem and project adapter. A citation, outline, or axiom is not a produced proof.
