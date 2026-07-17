# Opus 4.8 Synthesis — Class-Field Tame-Residue Graph Repair (mutation-ready, NOT applied)

**Mode:** read-only, difficulty 10. Idele tranche FROZEN. No repo file, task state, source row, or
graph row edited. **Verdict: `READY-FOR-GPT-REVIEW`.**

## Context

`localTameAbelianInertiaGroup` (`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:178`,
TODO@176) is a proxy carrier for `J_v = ker(I_v → k(v)ˣ)` whose canonical-kernel characterization is
unproved. It sits on the live MLT critical path. Stage-10 (Opus) proposed a standalone T1 obligation
`FLT-TAME-RESIDUE`; stage-11 (GPT-5.6 xhigh) returned `REVISE — substantive` (fixed a wild-inertia
misstatement, a consumer misassignment, and a missing closedness prerequisite; raised `lean_risk`);
stage-12 (Fable 5) returned an independent `DESIGN-VIABLE` design with buildable proof text. This
document merges the three into one mutation-ready design and re-verifies every cited signature against
the pinned source (toolchain `leanprover/lean4:v4.32.0-rc1`). Nothing here is applied.

### Probe-execution caveat (honest limitation)
Plan-mode is read-only, so I could **not** run `lake`/`lean` disposable probes myself. Instead I
verified, by reading the pinned source, that **every cited API exists** and that the proof terms in
§3 reference only lemmas that exist. Stage-11 and stage-12 *independently* reported green probes
(standard trio) for the same declarations. The apply-time gate (§7) still requires the actual compile.
Treat "elaborates" below as "API-verified + twice independently probed", not "I compiled it".

---

## §1 — Mathematics preserved: `P_v ≤ J_v ≤ I_v`, no universal strictness

Let `I_v = localInertiaGroup v`, `J_v = localTameAbelianInertiaGroup v`, `P_v` = wild inertia
(commentary only — **no Lean symbol**; `grep wildInertia` = 0 hits, so `P_v` is never a Lean claim).

- `J_v = ker(t_v : I_v → k(v)ˣ)`. `k(v)ˣ` has order `q−1` prime to `p = char k(v)`; the pro-`p` group
  `P_v` maps trivially, so **`P_v ≤ J_v`**. Wild inertia is **NOT excluded** from `J_v`.
  **Stage-10's "wild inertia excluded" claim is REFUTED; stage-11/12's correction is adopted.**
- **`J_v ≤ I_v`** is the only subgroup relation proved in Lean, and it is a `≤`, **never** `=`.
- **No universal strictness.** Witness inside the def's own carrier: at a place with `k(v) = 𝔽₂`,
  `Nat.card (κ 𝒪ᵥ) − 1 = 1`, the carrier degenerates to `∀ x ∈ fixedField I_v, σ x = x`, i.e.
  `J_v = I_v`. So `J_v < I_v` fails at every residue-field-`𝔽₂` place. Never assert `J_v = I_v`
  universally either — the two symbols stay type-level distinct.
- `narrowTraceConditionFunctor` (`LiftFunctor.lean:138`) stays on **full** inertia `I_v`; never
  retargeted to the tame subgroup (CE-A).

## §2 — The two support signatures + standard-trio proofs (exact)

Verified APIs (pinned): `AddSubgroup.mem_inertia` (`Mathlib/Algebra/Group/Subgroup/Basic.lean:1131`,
`:= .rfl`); `ContinuousSMulDiscrete` + `.isOpen_smul_eq`
(`FLT/Mathlib/Topology/Algebra/ContinuousSMulDiscrete.lean:32–33`, FLT-local);
`InfiniteGalois.fixingSubgroup_fixedField` (`Mathlib/FieldTheory/Galois/Infinite.lean:145`, takes a
**`ClosedSubgroup`** — this is *why* closedness gates containment). `localInertiaGroup` is literally
`(𝔪 …).toAddSubgroup.inertia (Γ Kᵥ)` (`AbsoluteGaloisGroup.lean:168`).

```lean
theorem AddSubgroup.isClosed_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M)
    (G : Type*) [Group G] [TopologicalSpace G] [MulAction G M] [ContinuousSMulDiscrete G M] :
    IsClosed (I.inertia G : Set G) := by
  have h : (I.inertia G : Set G) = ⋂ x : M, {σ : G | σ • x - x ∈ I} := by
    ext σ; simp [AddSubgroup.mem_inertia]
  rw [h]
  refine isClosed_iInter fun x ↦ ?_
  have hopen : ∀ S : Set M, IsOpen {σ : G | σ • x ∈ S} := fun S ↦ by
    have : {σ : G | σ • x ∈ S} = ⋃ y ∈ S, {σ : G | σ • x = y} := by ext σ; simp
    rw [this]; exact isOpen_biUnion fun y _ ↦ ContinuousSMulDiscrete.isOpen_smul_eq G x y
  rw [show {σ : G | σ • x - x ∈ I} = {σ : G | σ • x ∈ {y | y - x ∈ I}} from rfl, ← isOpen_compl_iff]
  exact hopen {y | y - x ∈ I}ᶜ

theorem isClosed_localInertiaGroup (v : Ω K) :
    IsClosed (localInertiaGroup v : Set (Γ Kᵥ)) :=
  AddSubgroup.isClosed_inertia _ _
```
Both audit to exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. No `IsClosed`-of-inertia
lemma exists anywhere in the pin (0 hits) — `AddSubgroup.isClosed_inertia` is the exact missing,
general, Mathlib-shaped lemma, and it **closes today** because the algebraic-extension
`ContinuousSMulDiscrete` instance and `continuousSMulDiscrete_integralClosure` already exist.
**This corrects stage-11**, which mislabeled closedness the "first actual Lean residual"; it is a
~15-LOC buildable unit, not an open residual.

## §3 — Exact new declarations (purely additive; zero consumer signature change)

Do **not** redefine `localTameAbelianInertiaGroup` (proxy carrier typechecks; consumer defeq must be
preserved). Add, same scope (`κ = IsLocalRing.ResidueField`, `Ω K = HeightOneSpectrum (𝓞 K)`, both
local-notation-confirmed at `AbsoluteGaloisGroup.lean:42–43`):

```lean
noncomputable def tameResidueChar (v : Ω K) : localInertiaGroup v →* (κ 𝒪ᵥ)ˣ := ...        -- GOAL
theorem localTameAbelianInertiaGroup_le_localInertiaGroup (v : Ω K) :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v := by                              -- proof text below
  intro σ hσ
  have hfix : σ ∈ (IntermediateField.fixedField (localInertiaGroup v)).fixingSubgroup := by
    rintro ⟨x, hx⟩; exact hσ x (pow_mem hx _)
  rwa [InfiniteGalois.fixingSubgroup_fixedField
    ⟨localInertiaGroup v, isClosed_localInertiaGroup v⟩] at hfix
theorem localTameAbelianInertiaGroup_eq_ker (v : Ω K) :
    localTameAbelianInertiaGroup v
      = (tameResidueChar v).ker.map (localInertiaGroup v).subtype := ...                    -- GOAL (TODO@176)
```
Containment closes today **given** §2 closedness; it is `≤`, never `=`.

**Tame residue character type = plain monoid hom `→*` (kept).** `#synth TopologicalSpace (κ 𝒪ᵥ)ˣ`
fails: `Mˣ` gets its topology only from `TopologicalSpace M` (`Mathlib/.../Constructions.lean:101`),
and `κ 𝒪ᵥ` carries none by default. A `→ₜ*` continuous variant does not elaborate.
*Harmless option, deliberately not taken:* `κ 𝒪ᵥ` is `Finite` (`AbsoluteGaloisGroup.lean:194`), so a
discrete `TopologicalSpace` could be supplied and would make the units continuous for free — but it is
**extra, unneeded plumbing** for every current consumer (all use `∈`/`≤ ker`, topology-free). Keep the
plain `→*`; only add discrete topology if a later consumer explicitly and harmlessly needs it.

## §4 — Exact proposed `FLT-TAME-RESIDUE` row + four consumer mutations

```text
obligation_id: FLT-TAME-RESIDUE
mathematical_name: Tame residue character and canonical kernel at a finite place
target_stage: T1
completion_targets: [T1, T2, T3]
current_state: definition-gap
critical_path: true
mathematical_novelty: standard
lean_risk: high                       # per R3 (§6); the closedness+containment prefix is demonstrably low
direct_dependencies: []               # see §5 — anything upstream creates a cycle
source_refs: [SRC-004]                # blueprint sketch only; SRC-004 is "Read; explicitly incomplete upstream"
expected_module: FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
kernel_probe_state: signature-green
lean_declaration: AddSubgroup.isClosed_inertia, isClosed_localInertiaGroup,
  localTameAbelianInertiaGroup_le_localInertiaGroup, tameResidueChar,
  localTameAbelianInertiaGroup_eq_ker
library_candidates: [localInertiaGroup, IsLocalRing.ResidueField, Subgroup.map,
  AddSubgroup.inertia, ContinuousSMulDiscrete, InfiniteGalois.fixingSubgroup_fixedField]
completion_gate: closedness, containment, tameResidueChar, and the kernel theorem compile; every new
  theorem audits to exactly [propext, Classical.choice, Quot.sound]; consumer signatures unchanged;
  graph regen yields exactly the four derived edges, no cycle, no reciprocity edge; primary Serre
  locator visually checked before any promotion past T1.
```

**Four consumer mutations** — append `"FLT-TAME-RESIDUE"` to `direct_dependencies` of each owner
(edge convention `E-{dep}-{node}`, direction dep→node, from `generate_graph.py:74–95`; regen only —
never hand-edit `proof-graph.ndjson`):

| Owner (record deps today) | Live consumer verified | Derived edge |
|---|---|---|
| `FLT-SGOOD-DEF` (`["FLT-HR-DEF"]`) | `BlueprintSGood.traceOnJ` `Conditions.lean:40` (`∀ σ ∈ localTameAbelianInertiaGroup v, trace = 2`) | `E-TAME-RESIDUE-SGOOD-DEF` **← the exact tame-kernel edge stage-7 demanded** |
| `FLT-SUPPORT-DEFORMATION` (`[]`) | `traceConditionFunctor` `LiftFunctor.lean:128` | `E-TAME-RESIDUE-SUPPORT-DEFORMATION` |
| `FLT-SGOOD-SELECTED` (`[FLT-SGOOD-DEF, …]`) | prospective `SelectedGood` "tame rank-one quotient at S" | `E-TAME-RESIDUE-SGOOD-SELECTED` (see duplicate note) |
| `FLT-CBASE` (`[FLT-AUT-DEF]`) | `cyclic_base_change`/`hρtame` `Automorphic.lean:186` (`localTameAbelianInertiaGroup w ≤ δ.ker`) | `E-TAME-RESIDUE-CBASE` |

**`traceConditionFunctor` owner resolved** (stage-10's open item): `FLT-SUPPORT-DEFORMATION`, whose
`lean_type` is "…lift-functor declarations in FLT/Deformations…"; `FLT-DEF-FUNCTOR` owns only the
specific `sGoodLiftFunctor_corepresentable`. Assignment defensible; residual ambiguity is low but
flag for GPT.

**`cyclic_base_change` owner resolved**: `FLT-CBASE.lean_declaration = cyclic_base_change` (verified);
stage-11's reassignment away from SGOOD-SELECTED-only is confirmed.

### Transitive-reduction duplicate (kept, not deleted)
In the current DAG `FLT-SGOOD-SELECTED.deps ⊇ {FLT-SGOOD-DEF}`, so `TAME-RESIDUE → SGOOD-SELECTED` is
**transitively implied** by `TAME-RESIDUE → SGOOD-DEF → SGOOD-SELECTED`:
```
FLT-TAME-RESIDUE ──→ FLT-SGOOD-DEF ──→ FLT-SGOOD-SELECTED
        ├──────────→ FLT-SUPPORT-DEFORMATION
        └──────────→ FLT-CBASE
```
**Keep the `FLT-SGOOD-SELECTED` insertion anyway.** This graph's edge semantics is *direct symbol
consumption*, `generate_graph.py` performs **no** transitive reduction, and `SelectedGood`'s own
signature will name the subgroup ("tame rank-one quotient at S" in its `lean_type`). Honest nuance the
task demands: this direct use is **prospective** — `SelectedGood` is a *definition-gap* (no live Lean
`def SelectedGood` naming the subgroup yet), so today the edge is genuinely redundant, but it encodes a
real planned direct dependency, not a fabricated one. Deleting it would drop a genuine (future) direct
use; keeping it duplicates a transitive path. Both facts are stated; neither is silently collapsed.

### Edge-kind flag (minimal-change recommendation)
`FLT-TAME-RESIDUE` is not in `generate_graph.py`'s hardcoded `definition_obligations` set
(`{FLT-DEF-001, FLT-HR-DEF, FLT-SGOOD-DEF, FLT-AUT-DEF, FLT-COMPAT-DEF, FLT-RACAR-DEF}`), so all four
edges regenerate with `edge_kind: "theorem"`. **Recommendation: accept `theorem` kind** — it is a
cosmetic label in the justification string, affects neither cycle nor depth, and keeps the mutation
**data-only** (four `direct_dependencies` appends + one new record). Adding the id to
`definition_obligations` is an optional, separate code change; flag for GPT, do not bundle.

## §5 — Reciprocity / FLT-LOCAL-GALOIS / Serre kept OUT (verified, not asserted)

- **`direct_dependencies: []` — FLT-LOCAL-GALOIS upstream creates TWO cycles** (verified;
  `FLT-LOCAL-GALOIS.deps = [FLT-SGOOD-SELECTED, FLT-DEF-FUNCTOR]`):
  (1) `LOCAL-GALOIS → TAME-RESIDUE → SGOOD-DEF → SGOOD-SELECTED → LOCAL-GALOIS`;
  (2) `LOCAL-GALOIS → TAME-RESIDUE → SUPPORT-DEFORMATION → DEF-FUNCTOR → LOCAL-GALOIS`.
  This **resolves stage-10's open `[]` vs `[FLT-LOCAL-GALOIS]` question to `[]`** and strengthens
  stage-11 (two cycles, not one). Justified three ways: (a) no obligation *owns* `localInertiaGroup`
  or the `AbsoluteGaloisGroup` module; (b) the two support proofs (§2) close using only Mathlib +
  `FLT.Mathlib` — no obligation-owned Lean in their closure; (c) the cycles above.
- **No reciprocity edge.** No `IsLocalClassField`/`localReciprocity` symbol exists in the pin (0
  hits). `tameResidueChar` is built by elementary Kummer theory (§6). Edges from `FLT-CLASS-FIELD`,
  `T-LOCAL-RECIP`, any local/global reciprocity node, `FLT-AUX-LOCAL-FIELD`, or directly to
  `FLT-MLT`: **ABSENT, forbidden.** `FLT-CLASS-FIELD` keeps only its two existing out-edges;
  Skinner–Wiles CFT stays routed to `FLT-AUX-LOCAL-FIELD` (stop-loss S4).
- **Source gate (Serre) kept closed.** `SOURCE-REGISTER.md` holds SRC-001…SRC-025; **no** Serre
  *Local Fields* row. Do **not** add `SRC-026`; do **not** write any Serre proposition/section/page
  (none visually checked in this pipeline). Node `source_refs: [SRC-004]` only. `HIST-UNRESOLVED`
  blocks any T2 assumption until an exact Lean type **and** a visually-checked primary locator are
  independently reviewed → `FLT-TAME-RESIDUE` may build kernel-clean at **T1** but **cannot be
  promoted past T1** until that Serre row is verified. No historical assumption registered here.

## §6 — Smallest buildable slice, first arithmetic residual, elementary construction

**Bounded Lean units (in order; all purely additive, zero consumer signature change):**
- **U1 — smallest buildable slice (build NOW):** `AddSubgroup.isClosed_inertia` +
  `isClosed_localInertiaGroup` (~15 LOC, §2, standard trio today).
- **U2 — first genuine tame theorem (build NOW given U1):**
  `localTameAbelianInertiaGroup_le_localInertiaGroup` (~8 LOC, §3, standard trio).
- **U3 — first ARITHMETIC residual (R1):** reduction on tame roots of unity — injectivity of
  `μ_{q−1}(integral closure) → μ_{q−1}(residue field)` and `μ_{q−1}(κ̄) ≃ k(v)ˣ`, via separability of
  `X^{q−1} − 1 mod 𝔪` (`gcd(q−1, p)=1`). No such lemma in the pin. *Everything through U2 is
  topological / Galois-correspondence; U3 is where genuine arithmetic starts.*
- **U4:** `tameResidueChar` definition + `MonoidHom` proof (needs U3).
- **U5:** unit-root Hensel lemma in `fixedField (localInertiaGroup v)` (R3 — deepest; Henselian,
  non-complete valuation ring; justifies `lean_risk: high`).
- **U6:** `localTameAbelianInertiaGroup_eq_ker` (needs U3–U5) — discharges TODO@176.
- Audit-only probe `FLTMethodology/Probes/TameResidueBoundary.lean` may accompany U1: `#check` the
  five consumer signatures + `#print axioms` of the def layer only. **Signature evidence only**
  (`kernel_probe_state: signature-green`) — never mathematical discharge. Node stays `definition-gap`
  until U6 lands and audits.

**Elementary construction (no reciprocity):** for `σ ∈ I_v`, fix uniformiser `ϖ` of `Kᵥ` and a root
`x` of `X^{q−1} = ϖ` in `Kᵥᵃˡᵍ` (`q = Nat.card (κ 𝒪ᵥ)`); `(σx/x)^{q−1} = σϖ/ϖ = 1` so `σx/x ∈ μ_{q−1}`;
`t_v(σ) :=` residue of `σx/x` in `k(v)ˣ` via U3. Multiplicativity/root-independence from `σ` fixing
`μ_{q−1}`. Inputs: alg-closed root existence, separability of `X^{q−1}−1` over `k(v)`, Henselian root
lifting — **no** reciprocity map, `classField_package`, idele, or Frobenius normalization.
Orientation `t_v` vs `t_v⁻¹` recorded as a **convention** (all consumers use `∈`/`≤ ker`,
inversion-stable; stage-6 CE-7 preserved), never a compile-gating theorem.

## §7 — Axiom gates + source-verification gate

- **Axiom gate:** every new theorem audits to **exactly `[propext, Classical.choice, Quot.sound]`**,
  no `sorryAx`. Despite T1's global `knownin1980s` allowance, this node's own completion gate requires
  the **standard trio only**. (`cyclic_base_change` still carries `sorryAx` — separately owned by
  `FLT-CBASE`, untouched by this repair.)
- **Source-verification gate:** no SRC row may state an exact Serre proposition/page until visually
  checked; no `SRC-026` added now; promotion past T1 blocked until the primary locator is visually
  verified and independently reviewed.

## §8 — Stop-losses (carried forward)
- **S1 reciprocity:** any proof needing a reciprocity map / `classField_package` / an edge from
  `FLT-CLASS-FIELD` or a reciprocity node → STOP, return `REVISE`.
- **S2 conflation:** any `=` between `J_v` and `I_v`, any universal-strictness claim, any "wild
  inertia excluded" claim, any Lean statement about `P_v` → STOP.
- **S3:** retargeting `narrowTraceConditionFunctor` to the tame subgroup → STOP.
- **S4 source:** any SRC row with an unverified Serre locator, or promotion past T1 before visual
  verification → STOP.
- **S5 axioms:** any new theorem auditing beyond the standard trio, or treating probe/proxy as
  mathematical discharge → STOP; node stays `definition-gap` until U6.
- **S6 scope:** U5 exceeding ~300 LOC or needing completed-field machinery absent from the pin → pause
  and re-review rather than importing analytic infrastructure.

## §9 — Corrections to the source stages (source-faithful, not model-trusting)
1. **Stale grep claim:** stages 11 & 12 assert "no obligation names `localTameAbelianInertiaGroup` /
   0 hits." **False as stated** — `FLT-SGOOD-DEF.library_candidates` and `.source_condition_risks`
   both name it. The *substantive* conclusion (no obligation **owns** it via `lean_declaration`) still
   holds, so the standalone-node decision is unaffected; but the literal claim is corrected here.
2. **Register already narrates this pipeline:** `FLT-CLASS-FIELD.review_state =
   "tame-graph-synthesis-running"`, `FLT-CBASE.review_state = "diversity-design-queued"`, and several
   `estimates.evidence`/`source_condition_risks` fields already mention "tame-residue"/"Fable". These
   are review-log narrative, **not** graph mutations; no `FLT-TAME-RESIDUE` record or edge exists yet.
3. **Line-number fixes:** `traceConditionFunctor` `LiftFunctor.lean:128` (not :129);
   `narrowTraceConditionFunctor` `:138` (not :139); `cyclic_base_change` theorem `Automorphic.lean:137`.
4. **Closedness is not a residual** (corrects stage-11): it is buildable U1 today.
5. **Wild inertia** (corrects stage-10): `P_v ≤ J_v`, not excluded.

## Verification (for the eventual edit — NOT run here, plan-mode read-only)
1. `lake env lean` on U1/U2 declarations; `#print axioms` = standard trio for each landed unit.
2. `lake build FLTMethodology` stays green (frozen idele tranche untouched).
3. `python methodology/control/generate_graph.py`: exactly the four `E-TAME-RESIDUE-*` edges, no
   cycle, no unknown-dependency error, no `FLT-CLASS-FIELD → FLT-TAME-RESIDUE` edge.
4. Consumer files byte-identical.

## Open items flagged for GPT review (not fabricated, not decided)
- Confirm `FLT-SUPPORT-DEFORMATION` as `traceConditionFunctor` owner (low residual ambiguity vs
  `FLT-DEF-FUNCTOR`).
- Confirm edge-kind decision: accept `theorem` kind (recommended, data-only) vs add
  `FLT-TAME-RESIDUE` to `generate_graph.py:definition_obligations`.
- Confirm keeping the transitively-redundant `FLT-SGOOD-SELECTED` edge given its direct use is
  currently *prospective* (SelectedGood is a definition-gap).
- Re-run the U1/U2 compile probes at apply time (plan-mode blocked execution here).

**Verdict: `READY-FOR-GPT-REVIEW`.** No graph mutation applied; no source row added; no historical
assumption registered.
