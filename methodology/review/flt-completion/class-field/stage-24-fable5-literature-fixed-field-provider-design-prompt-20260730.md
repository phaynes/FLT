# Literature-grounded design — close the FLT tame-residue fixed-field provider

Read-only design. Do not edit files, commit, or change task state. Return an implementable proof
design and source-to-Lean map, not a broad literature summary.

Repository:
`/Volumes/second-store/devel/proof-forks/FLT-tame-residue-completion-20260730`

Frozen design base: `67cddb6b0ce0cffdb2810320d39d8d2e7e9d1bd5`

Exact target:

```lean
FixedFieldUniformizerDecomposition v
```

in `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`. The current source already
constructs the tame residue character and conditionally proves the final kernel theorem. The target
build is 3,443 jobs green, the umbrella build is 9,045 jobs green, and all declarations currently
printed by `FLTMethodology.Probes.TameResidueBoundary` audit to exactly
`[propext, Classical.choice, Quot.sound]`. The provider itself is only a `Prop`, with no witness.

Use these independently reviewed prior artifacts as literature/design evidence, while rechecking
their claims against the current target and pinned APIs:

- `/Volumes/second-store/devel/proof-forks/FLT-fixed-field-value-group-20260719/methodology/source-design/tame-fixed-field-uniformizer.md`
- `/Volumes/second-store/devel/proof-forks/FLT-fixed-field-value-group-20260719/methodology/evidence/reviews/THM-TAME-FIXED-FIELD-LITERATURE-OPUS48-INDEPENDENT-REVIEW-20260719.md`
- `/Volumes/second-store/devel/proof-forks/FLT-fixed-field-value-group-20260719/FLTMethodology/Probes/FixedFieldValueGroupBridge.lean`
- `/Volumes/second-store/devel/proof-forks/FLT-fixed-field-value-group-20260719/methodology/evidence/reviews/THM-TAME-FIXED-FIELD-VALUE-GROUP-BRIDGE-BUILD-20260719.md`
- `/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-019-wiese-galois-representations.qmd`

The prior source gate cites J. Neukirch, *Algebraic Number Theory*, Chapter II section 3,
Proposition 3.8 and following paragraph; section 7, Definition 7.4 and Proposition 7.5; and section
9, Definition 9.10 and Proposition 9.11. It records PDF SHA-256
`a6d883b38fa7adc661248219d8611cc18dd22a1e6dd4ac3646be0aa6e6f4607c` and the source URL
`https://web.math.ucsb.edu/~agboola/teaching/2021/fall/225A/neukirch.pdf`. Treat the retained
independent review as evidence of those checked locators, but distinguish it from a current local
copy and from Lean implementation.

Tasks:

1. Revalidate the exact mathematical statement and source-to-Lean hypothesis translation.
2. Inspect current pinned APIs and the prior kernel-clean normality/Galois probe. Decide exactly
   what can be ported and what remains missing.
3. Recursively expand the finite-subextension, inertia, ramification-index-one, valuation-lies-over,
   integral-unit, and fixedness steps until each leaf is executable or explicitly unavailable.
4. Give exact proposed Lean signatures and named existing theorem dependencies in build order.
5. Test direct and finite-subextension routes; identify the one with highest verified closure
   probability, not the shortest prose proof.
6. State counterexamples prevented by each hypothesis and identify any source/statement mismatch.
7. Give the first bounded implementation slice, its build/axiom probes, and stop-loss rule. Do not
   introduce a historical axiom or restate the provider as an assumption.

End with one verdict: `IMPLEMENTABLE-NOW`, `IMPLEMENTABLE-AFTER-NAMED-LIBRARY-BRIDGE`, or
`STATEMENT-REPAIR-REQUIRED`, followed by the exact reason.
