# Independent Stage-1 design: `cyclic-base-change` / `FLT-CBASE`

Repository: `/Volumes/second-store/devel/proof-forks/FLT`  
Frozen design baseline: branch `methodology/varro-proof-program-20260716`, SHA
`827eb969aff49fb5c5a1b17f807426d3be1b4056`  
Pipeline: `tri-design-synthesis-build`, stage 1, independent read-only design  
Disposition: produce  
Target stage: T2 and ultimately T3 standard-axiom closure.

Act as an independent source-faithful mathematical and Lean architect. Read the repository, but do
not edit it or create files. Do not use another model's design. This is a fresh one-shot design.

The repository already exports an admitted theorem `cyclic_base_change` in
`FLT/GaloisRepresentation/Automorphic.lean`. It states an iff for the repository-specific
quaternionic `GaloisRep.IsAutomorphicOfLevel` predicate across a finite solvable Galois extension of
totally real fields, under irreducibility, cyclotomic determinant, integral flat model,
unramifiedness, and tame-rank-one quotient hypotheses. The graph warns that downstream work may
also require image characterization, multiplicity one, descent/twist control, local compatibility,
and coefficient transport. Do not assume the existing iff silently supplies any of those.

Inspect at least:

- the complete definition of `GaloisRep.IsAutomorphicOfLevel` and complete exact type/docstring of
  `cyclic_base_change` in `FLT/GaloisRepresentation/Automorphic.lean`;
- every textual and typed consumer of `cyclic_base_change`, distinguishing real Lean applications
  from methodology probes and future graph edges (`FLT-MLT`, `FLT-BRAUER-FAMILY`);
- `FLT.Components.Existing`, adapter audits, library-match probes, `FLT-MLT-SOURCE`, `FLT-CBASE`,
  `FLT-POTMOD`, `FLT-BRAUER-FAMILY`, `FLT-JL`, and automorphic/Galois support rows;
- `methodology/SOURCE-REGISTER.md`, especially the incomplete `SRC-004` blueprint and any primary
  solvable/cyclic base-change references actually available in the tree;
- pinned FLT/Mathlib APIs for field extensions, restriction (`GaloisRep.map`), place pullback,
  automorphic forms, Hecke systems, characters/twists, local conditions, and scalar extension.

Return one implementable report with these exact sections:

1. **Observed baseline and exact consumers.** Reproduce the current theorem type accurately, list
   all actual consumers and graph-only planned consumers, and itemize the exact conclusion each
   needs. State whether the theorem is cyclic, solvable, or a solvable iteration despite its name.
2. **Source theorem boundary.** Give primary source theorem(s), exact locators, hypotheses, and
   conclusions for transfer and descent. Mark unavailable/unverified sources. Explain any mismatch
   between classical GL2 base change and the repository's very specific quaternionic
   `IsAutomorphicOfLevel` predicate.
3. **Minimal component split.** Separate forward transfer, descent/image characterization,
   character twists, strong multiplicity one, local/conductor compatibility, and coefficient
   transport only as required by observed consumers. Reject a monolithic theorem whose hypotheses
   encode the conclusion.
4. **Exact Lean signatures in dependency order.** Give namespace, universes, variables, typeclass
   assumptions, and full Lean theorem types. Label every dependency `EXISTING-PROVED`,
   `EXISTING-ADMITTED`, or `PROPOSED`. Identify whether to retain, narrow, split, or replace the
   current public theorem while preserving downstream scope.
5. **Pinned-library matches.** Give exact checked declarations and classify exact/adaptable/
   signature-only/missing. Do not count the admitted `cyclic_base_change` as a proved library match.
6. **Counterexamples and statement risks.** Test irreducibility after restriction, cyclic versus
   solvable hypotheses, even-degree requirements, pullback of level, ramification/tame quotient
   transport, coefficient and representation-space identification, descent up to twist, invariant
   characters, multiplicity one, endpoint orientation, and circular dependence on potential
   automorphy or modularity lifting.
7. **Smallest buildable first slice.** Specify a bounded first production module/signature tranche,
   targeted `lake build` and `#print axioms` commands, and the first likely residual Lean goal. A
   source-exact interface scaffold must be labelled as such, not called a proof.
8. **Dependency graph and gates.** Give the local DAG, completion condition, and stop-loss gates for
   source mismatch, false iff direction, missing automorphic representation vocabulary, or an
   unformalized analytic theorem that must remain a named T2 boundary rather than a fake T3 proof.
9. **Verdict.** Return exactly one of `DESIGN-VIABLE`, `INTERFACE-FIRST`, or `OBSTRUCTION`, followed
   by a concise reason and the next exact theorem/signature to attempt.

Preserve the frozen games—here, the exact current theorem scope, endpoints, and public target. Do
not introduce a generic base-change authority axiom, and do not claim T3 closure without a
kernel-clean proof and declaration axiom audit.

