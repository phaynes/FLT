# GPT-5.6 xhigh independent review — class-field tame-residue graph synthesis

REVISE-MECHANICAL

The mathematics, Lean boundary, and dependency design agree. The blocker is that the proposed control row is not mutation-ready as written.

- Exact mathematics is `P_v ≤ J_v ≤ I_v`. Counterchecks:
  - The exact `Nat.card k(v) = 2 → J_v = I_v` theorem compiled with `[propext, Classical.choice, Quot.sound]`, refuting universal strictness.
  - Over `ℚ₃`, inertia in `ℚ₃(√3)/ℚ₃` moves `√3`, refuting universal equality.
  - Over `ℚ₂`, `J_v = I_v` while wild inertia is nontrivial, refuting wild-inertia exclusion.
- The rerun [controller probe](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/class-field/stage-14-controller-u1-u2-kernel-probe.md:19) exited 0. U1 closedness and U2 containment each audit to exactly the standard trio.
- The plain `localInertiaGroup v →* (κ 𝒪ᵥ)ˣ` type and mapped-kernel orientation elaborate. The continuous version fails because the target has no inferred topology. U3–U6 remain absent and unproved.
- `FLT-TAME-RESIDUE` with no dependencies is acyclic. Current simulation gives four exact edges and no reciprocity or `FLT-LOCAL-GALOIS` dependency. The prospective `FLT-SGOOD-SELECTED` edge should be **kept**: its current methodology boundary already names the subgroup directly in [HasGenericTameRankOneQuotient](/Volumes/second-store/devel/proof-forks/FLT/FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean:37).
- `FLT-SUPPORT-DEFORMATION` is the correct coarse owner for [traceConditionFunctor](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/LiftFunctor.lean:127). The generated `theorem` edge-kind is metadata-only and harmless.
- Source promotion remains closed: [SRC-004](/Volumes/second-store/devel/proof-forks/FLT/methodology/SOURCE-REGISTER.md:12) is explicitly incomplete and there is no visually verified *Local Fields* locator.

Mechanical repairs required:

1. The “exact” [proposed row](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/class-field/stage-13-opus48-tame-graph-synthesis.md:105) omits six schema-required fields after generation: `lean_type`, `stage_completion`, `source_condition_risks`, `proof_pattern`, `estimates`, and `review_state`. The requirements are explicit in the [instance schema](/Volumes/second-store/devel/proof-forks/FLT/methodology/spec/flt-proof-program.instances.schema.json:42).
2. Its axiom gate should cover every new declaration, including `tameResidueChar`, not only “every new theorem.”
3. `HIST-UNRESOLVED` should be described as blocking any new tame-residue historical assumption; the ledger now contains unrelated permitted T2 assumptions.
4. Stage 12’s 52-record count is stale; the current register has 53, so adding this node would produce 54.

Therefore this verdict authorizes neither adding the row/edges nor beginning implementation yet. After those mechanical corrections, the accepted scope is the row plus all four edges and only U1/U2—not U3–U6, T2 promotion, full class-field completion, or any historical assumption. No repository files were edited.
