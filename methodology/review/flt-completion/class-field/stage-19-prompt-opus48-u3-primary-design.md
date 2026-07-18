# Opus 4.8 primary design — tame-residue U3 roots-of-unity reduction

Act as a read-only hostile mathematical and Lean designer at difficulty 8. Review the exact commit
supplied by the launch wrapper in `/Volumes/second-store/devel/proof-forks/FLT`. Temporary Lean
probes outside the repository are allowed. Do not edit source, control artifacts, task state, or git.

The U1/U2 prefix is frozen and independently sealed. Design only U3, the smallest arithmetic bridge
needed before `tameResidueChar`; do not attempt U4–U6, reciprocity, source authorization, or component
promotion.

Read in full:

- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`;
- `FLTMethodology/Probes/TameResidueBoundary.lean`;
- `methodology/review/flt-completion/class-field/stage-12-fable5-tame-graph-diversity.md`;
- `methodology/review/flt-completion/class-field/stage-13-opus48-tame-graph-synthesis.md`;
- `methodology/review/flt-completion/class-field/stage-15-gpt56xhigh-tame-graph-review.md`;
- `methodology/review/flt-completion/class-field/stage-17-controller-u1-u2-bounded-build.md`;
- `methodology/review/flt-completion/class-field/stage-18-opus48-tame-u1-u2-build-review.md`;
- the exact current `FLT-TAME-RESIDUE` obligation and its four outgoing edges.

Deliver:

1. State the exact mathematical U3 theorem actually needed by U4. Separate any logically distinct
   claims: reduction injectivity on prime-to-residue-characteristic roots of unity, existence or
   surjectivity onto residue-field units, and identification with a cyclic group. Do not combine
   non-equivalent claims into an omnibus theorem.
2. Locate the strongest existing Lean APIs at this pinned Mathlib revision for roots of unity,
   valuation/integral-closure reduction, residue fields, separability, Henselian lifting, and finite
   field units. Give exact declaration names and `#check` outputs; say explicitly when infrastructure
   is absent.
3. Provide the smallest complete Lean signature with all universes, instances, maps and domains made
   explicit. Prefer a reusable algebraic lemma over a place-specific wrapper only if the generic
   hypotheses can actually be instantiated for `IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)`.
4. Use temporary probes to elaborate every proposed signature. If feasible, prove the structural or
   finite-field sublemmas and audit them to exactly `[propext, Classical.choice, Quot.sound]`.
5. Identify precisely which part is U3 and which part really belongs to U5 Henselian lifting. In
   particular, do not assume reduction injectivity from Hensel existence, completeness of the
   unramified fixed field, or local class-field reciprocity.
6. Give the minimal dependency graph from existing declarations to the proposed U3 theorem and the
   first expected residual Lean goal. Include stop-loss counterexamples for missing coprimality,
   nonintegral roots, non-Henselian rings, and residue characteristic dividing the exponent.
7. Recommend exactly one bounded next action: `BUILD-U3-SLICE`, `REPAIR-U3-STATEMENT`, or
   `OBSTRUCTION-DECOMPOSE`, with the files/declarations it may add. It must not authorize U4–U6 or
   change the public subgroup definition.

Return exactly one verdict: `READY-FOR-GPT-REVIEW`, `REVISE`, `OBSTRUCTION`, or `NO-RESULT`, followed
by the requested evidence. The Lean kernel and exact axiom audits remain final authority.
