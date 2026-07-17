INDEPENDENT GPT-5.6 XHIGH RE-REVIEW — CLASS-FIELD REPAIRED DESIGN

Review read-only:

- `stage-1-opus48-primary.md`
- `stage-2-gpt56xhigh-review.md`
- `stage-3-opus48-repair.md`

against `FLT-CLASS-FIELD`, the exact source register, graph consumers, target-stage policy, and
pinned Lean APIs. Verify that the repaired design actually resolves every Stage-2 finding:

1. `IsFiniteOrderCharacter` uses a nontrivial rank-one `GaloisRep F A A` carrier;
2. `HasPrescribedLocalComponents` is a same-carrier relation reusing `χ.toLocal`;
3. Skinner–Wiles/global solvable-field work is routed out of class-field and the graph mismatch is
   exposed rather than hidden;
4. induced-representation determinant/conductor bookkeeping is removed from CF-COMPAT;
5. local reciprocity and the derived inertia-to-residue map have the correct direction and ownership;
6. partial existing idele, local inertia, and Galois-abelianization infrastructure is reused honestly;
7. every interface marked T2-nameable has an exact type and primary locator; unresolved full
   reciprocity/globalization remains explicitly non-nameable.

Read-only test the proposed first `ClassFieldCharacterBoundary` signatures in temporary Lean. Return
exactly one leading verdict: `PASS`, `REVISE`, `UNCERTAIN`, or `REFUTED`. State whether Fable is
triggered under the conditional-only ladder and give the next exact kernel probe/build unit. Do not
edit repository files, register axioms, promote obligations, or treat interface elaboration as a
mathematical proof.
