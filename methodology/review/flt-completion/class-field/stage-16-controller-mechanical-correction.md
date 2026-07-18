# Controller mechanical correction — tame-residue mutation packet

Date: 2026-07-18 (Australia/Sydney)

This packet applies only the four mechanical corrections required by the independent Stage-15
review. It changes no proof obligation, graph edge, Lean source, historical assumption, or target
stage. Its purpose is to make the accepted mutation exact before implementation begins.

## 1. Complete-schema obligation row

The mutation must use all current schema-required fields:

```json
{"obligation_id":"FLT-TAME-RESIDUE","mathematical_name":"Tame residue character and canonical inertia kernel at a finite place","lean_declaration":"AddSubgroup.isClosed_inertia; isClosed_localInertiaGroup; localTameAbelianInertiaGroup_le_localInertiaGroup; tameResidueChar; localTameAbelianInertiaGroup_eq_ker","lean_type":"Definition gap: U1 proves inertia closedness and U2 proves the repository proxy J_v is contained in inertia I_v. Remaining U3-U6 must construct the plain tame residue monoid hom localInertiaGroup v ->* (kappa O_v)^x and prove the existing localTameAbelianInertiaGroup equals its mapped kernel.","target_stage":"T1","source_refs":["SRC-004"],"current_state":"definition-gap","direct_dependencies":[],"graph_depth":0,"scc_id":"SCC-FLT-TAME-RESIDUE","critical_path":true,"library_candidates":["AddSubgroup.inertia","ContinuousSMulDiscrete","InfiniteGalois.fixingSubgroup_fixedField","IsLocalRing.ResidueField","Subgroup.map"],"source_condition_risks":"SRC-004 is explicitly incomplete and no primary Local Fields locator has been visually verified. P_v <= J_v <= I_v is the reviewed relation; universal equality, universal strictness, and wild-inertia exclusion are false. U3 roots-of-unity reduction injectivity, U4 tameResidueChar, U5 Henselian lifting, and U6 the kernel theorem remain open.","mathematical_novelty":"standard","lean_risk":"high","proof_pattern":"Bank the topology and Galois-correspondence prefix U1/U2 with standard axiom closure, then prove roots-of-unity reduction, construct the elementary tame character without reciprocity, prove the required root lifting, and identify the proxy with the mapped kernel.","expected_module":"FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup","estimates":{"loc_p50":700,"loc_p80":4000,"loc_p95":18000,"tokens_p50":100000,"tokens_p80":650000,"tokens_p95":3500000,"confidence":"low","evidence":"U1/U2 compile with the standard trio. U3-U6 are absent; U5 is the deepest Henselian arithmetic boundary."},"review_state":"bounded-u1-u2-build-authorized-after-mechanical-correction","kernel_probe_state":"temporary-u1-u2-standard-trio-green","completion_gate":"All five named declarations exist and each audits to exactly [propext, Classical.choice, Quot.sound]; U3-U6 and a visually verified primary source locator are complete; consumer signatures remain unchanged; no reciprocity edge or historical assumption is introduced.","completion_targets":["T1","T2","T3"],"stage_completion":"T1 closes only after tameResidueChar and localTameAbelianInertiaGroup_eq_ker are proved with standard axiom closure. T2 and T3 retain the same theorem and source requirements; no tame-residue T2 assumption is presently authorized."}
```

## 2. Exact graph delta

The new node has no dependencies. Append `FLT-TAME-RESIDUE` to exactly these four consumers:

- `FLT-SGOOD-DEF`;
- `FLT-SUPPORT-DEFORMATION`;
- `FLT-SGOOD-SELECTED`;
- `FLT-CBASE`.

No edge may target `FLT-CLASS-FIELD` or `FLT-LOCAL-GALOIS`; either would misstate ownership and the
latter would create cycles. The generator's `theorem` edge label is accepted as metadata-only.

The live pre-mutation register has 54 nodes and 98 edges. This delta must regenerate to exactly 55
nodes and 102 edges with zero cycles.

## 3. Declaration-wide axiom gate

The gate applies to every declaration introduced on this path, definitions included. In the bounded
build it covers all three landed U1/U2 declarations. When U4 is attempted it must separately audit
`tameResidueChar`; when U6 is attempted it must separately audit the kernel theorem. The accepted
surface is exactly `[propext, Classical.choice, Quot.sound]` for each declaration.

## 4. Historical-assumption gate

`HIST-UNRESOLVED` blocks any new tame-residue historical assumption. Existing, unrelated authorized
T2 boundaries do not change this. This tranche must not edit `historical-assumptions.ndjson`, add a
Serre source row, or promote `FLT-TAME-RESIDUE` beyond `definition-gap`.

## Corrected next action

The four Stage-15 mechanical defects are now made explicit. The accepted bounded next action is to
apply this exact row and edge delta and persist U1/U2 only, followed by the declaration-wide axiom
audit, both umbrella builds, graph/count/cycle checks, and an independent build review. U3-U6 remain
out of scope for that build.
