# Independent Stage-1 design: `class-field` / `FLT-CLASS-FIELD`

Repository: `/Volumes/second-store/devel/proof-forks/FLT`  
Frozen design baseline: branch `methodology/varro-proof-program-20260716`, SHA
`827eb969aff49fb5c5a1b17f807426d3be1b4056`  
Pipeline: `tri-design-synthesis-build`, stage 1, independent read-only design  
Disposition: interface  
Target stage: T2 initially; the same mathematical obligations ultimately require standard-axiom
T3 proofs.

Act as an independent source-faithful mathematical and Lean architect. Read the repository, but do
not edit it or create files. Do not use another model's design. This is a fresh one-shot design.

The graph currently proposes `FLT.PotentialModularity.classField_package`, but no such declaration
exists. `FLT-CLASS-FIELD` is a definition gap, not a theorem already waiting for tactics. The only
direct graph consumers are the still-absent `FLT.PotentialModularity.induced_rep_isAutomorphic`
(`FLT-INDUCED-MOD`) and `FLT.PotentialModularity.exists_auxiliary_curve` (`FLT-AUX-CURVE`). The
source register currently points only to the incomplete chapter-4 blueprint (`SRC-004`), so do not
treat that citation as an exact source theorem. In particular, reject a single generic package
whose fields merely assume every consequence the downstream proof wants.

Inspect at least:

- `methodology/control/proof-obligations.ndjson`, `proof-graph.ndjson`,
  `library-matches.ndjson`, `source-design.ndjson`, and `component-bom.ndjson`;
- `methodology/SOURCE-REGISTER.md`, `TRACEABILITY.md`, `MLT-SOURCE-CONTRACT.md`, and the chapter-4
  blueprint source cited as `SRC-004`;
- every existing and proposed downstream consumer of `FLT-CLASS-FIELD`, distinguishing actual Lean
  declarations from graph-only prose;
- pinned Mathlib and FLT declarations around `NumberField.AdeleRing`, local and global reciprocity,
  `IsLocalClassField`, continuous characters, induced representations, local prescriptions,
  conductors, restriction/norm compatibility, and extension of finite-order characters.

Return one implementable report with these exact sections:

1. **Observed baseline and exact consumers.** List every actual Lean consumer and every planned
   graph consumer separately, with file/declaration references. State exactly what each consumer
   needs; do not infer unused class-field theory.
2. **Source theorem boundary.** Identify primary theorem(s), exact locators, hypotheses, and
   conclusions for each required fact. Mark any unverified locator or mismatch. Explain why
   `SRC-004` alone is insufficient.
3. **Minimal component split.** Replace `classField_package` with the smallest collection of
   separately named definitions and theorems that has stable contracts. Separate local reciprocity,
   global reciprocity, character construction/local prescription, and compatibility only where the
   observed consumers require them.
4. **Exact Lean signatures in dependency order.** Give namespace, universes, variables, typeclass
   assumptions, and full proposed theorem types in Lean syntax. Label every referenced declaration
   `EXISTING-PROVED`, `EXISTING-ADMITTED`, or `PROPOSED`. Do not hide mathematics in an opaque
   structure field, generic `Prop`, or class-field authority hypothesis.
5. **Pinned-library matches.** Report exact declaration names and where found. Distinguish exact,
   adaptable, signature-only, and missing matches. Do not claim a match without checking its actual
   type.
6. **Statement risks and counterexamples.** Test local/global direction, continuity/topology,
   finite-order and ramification conditions, local prescription compatibility/product formula,
   coefficient/codomain issues, extension/restriction direction, and any circular use of the
   auxiliary-curve or induced-modularity target.
7. **Smallest buildable first slice.** Specify the first production module and exact signatures that
   should elaborate now with no `sorryAx`, plus targeted `lake build` and `#print axioms` commands.
   An honest interface-only slice may be definitions and adapters, but may not masquerade as the
   missing theorem.
8. **Dependency graph and gates.** Give the component-local DAG, completion gate, and stop-loss
   conditions. State what evidence would advance DoR and what would force redesign or source work.
9. **Verdict.** Return exactly one of `DESIGN-VIABLE`, `INTERFACE-FIRST`, or `OBSTRUCTION`, followed
   by a concise reason and the next exact theorem/signature to attempt.

The design must preserve the current FLT theorem scope and target-stage axiom policy. It must not
add an assumption equivalent to potential modularity, automorphic induction, or auxiliary-curve
existence under the name “class field theory.”

