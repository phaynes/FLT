# GPT-5.6 xhigh independent review — class-field tame-residue graph synthesis

**Mode:** independent read-only review.  
**Verdict:** `REVISE-MECHANICAL`.

The mathematical design is accepted, subject to the mechanical corrections and bounded scope below.
This verdict authorizes adding the corrected open `FLT-TAME-RESIDUE` obligation and its four direct
consumer edges, and implementing only the kernel-green U1/U2 prefix. It does not authorize U3--U6,
a historical assumption, source promotion, or discharge of `FLT-TAME-RESIDUE` or
`FLT-CLASS-FIELD`.

## Mathematical findings

- The subgroup relation is `P_v ≤ J_v ≤ I_v`: wild inertia is contained in the tame-kernel proxy,
  not excluded from it.
- Universal strictness is false. At residue cardinality two, the proxy can equal full inertia.
- Universal equality is also false; the reviewed ramified `Q_3(sqrt 3)` example separates the two.
- The reviewed `Q_2` example independently refutes the earlier wild-inertia-exclusion claim.
- The controller U1/U2 probe compiles and each of its three declarations audits to exactly
  `[propext, Classical.choice, Quot.sound]`.
- The plain monoid-hom target for `tameResidueChar` elaborates. A continuous-monoid-hom signature
  does not elaborate without adding target topology that no current consumer requires.
- U3--U6 are absent and remain genuine arithmetic work. The proxy is therefore not yet identified
  with a canonical tame-residue kernel.

## Graph verdict

Adding a source-open `FLT-TAME-RESIDUE` node with no upstream obligation dependency is acyclic. Keep
the four reviewed direct-consumer edges to:

1. `FLT-SGOOD-DEF`;
2. `FLT-SUPPORT-DEFORMATION`;
3. `FLT-SGOOD-SELECTED`;
4. `FLT-CBASE`.

There is no reciprocity or `FLT-CLASS-FIELD` dependency. The direct selected-good edge is retained as
prospective direct symbol consumption even though a transitive path also exists.

## Mandatory mechanical corrections

1. The new obligation row must include the complete current schema, including `lean_type`,
   `stage_completion`, `source_condition_risks`, `proof_pattern`, `estimates`, and `review_state`.
2. The declaration-level axiom gate must cover every persisted declaration, including any eventual
   `tameResidueChar`; in the bounded U1/U2 build it covers all three declarations actually added.
3. `HIST-UNRESOLVED` forbids registering a new tame-residue historical assumption. No source row or
   T2 boundary may be added by this tranche.
4. Use the graph's live count at mutation time. The pre-existing count observed by the reviewer is
   stale whenever another independently governed node has landed.

## Authorized bounded action

Persist U1/U2 only:

- `AddSubgroup.isClosed_inertia`;
- `isClosed_localInertiaGroup`;
- `localTameAbelianInertiaGroup_le_localInertiaGroup`.

Keep `FLT-TAME-RESIDUE.current_state = definition-gap`; record U3 roots-of-unity reduction as the
first arithmetic residual. Do not define `tameResidueChar`, assert the kernel theorem, mutate consumer
Lean signatures, or promote either obligation.

No repository file, task state, graph row, or historical-assumption row was edited by this reviewer.
