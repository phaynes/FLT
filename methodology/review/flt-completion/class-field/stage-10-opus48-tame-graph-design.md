# Bounded Design — Class-Field Tame-Residue Graph Ownership

**Mode:** read-only, difficulty 10. Idele object/type tranche is FROZEN (not reopened).
**Verdict:** `READY-FOR-GPT-REVIEW` (with two prompt-locator corrections, see §0).

---

## Context

The class-field reviews (stage-6 synthesis, stage-7 GPT-5.6 xhigh, stage-8 build) isolated one
*elementary* boundary that is currently a definition gap sitting on the live modularity-lifting (MLT)
critical path: the tame-residue kernel. The repository symbol `localTameAbelianInertiaGroup` is
defined by a **proxy carrier** with an open `TODO: show that this is indeed the right group`. Three
real Lean consumers depend on that symbol. Stage-6 named the node `T-TAME-RESIDUE` / `T1`, kept it
explicitly OFF the class-field-theory path, and forbade the edge `T-LOCAL-RECIP → T1`. Stage-7
required the graph repair to name the *exact* tame-kernel edge to `FLT-SGOOD-DEF` (a generic
"class-field → MLT" edge is insufficient) and to reconcile `FLT-AUX-LOCAL-FIELD` / Skinner–Wiles
ownership. No obligation was promoted and no Lean was built in any of those read-only passes.

This document is the smallest exact proof-program repair. It is a **design deliverable**, not a code
change; nothing here is applied.

---

## §0 — Prompt-locator corrections (must be carried into any edit)

1. `localTameAbelianInertiaGroup` is defined at **`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:170–184`**, TODO at **line 176**. The prompt's path `FLT/NumberField/AbsoluteGaloisGroup.lean` **does not exist**.
2. The third consumer's hypothesis is **`hρtame`** (Greek ρ) at `FLT/GaloisRepresentation/Automorphic.lean:186`, not `hrhoTame`. The whole theorem `cyclic_base_change` is `sorry` at `Automorphic.lean:194` (a *separate* obligation, not discharged by this repair).
3. New-obligation string is **`FLT-TAME-RESIDUE`** (prompt form); reviews call the node `T-TAME-RESIDUE`/`T1`. No `obligation_id` in the 52-record register currently contains `TAME`, `RESIDUE`, or `INERTIA`, so the id is free to add.

---

## §1 — Decision: add a new `FLT-TAME-RESIDUE` obligation (T1)

**Decision: ADD a new obligation `FLT-TAME-RESIDUE`, `target_stage: T1`, `current_state: definition-gap`,
that OWNS `localTameAbelianInertiaGroup` + its kernel-characterization theorem, off the reciprocity
path.** The stage-7 "exact edge to `FLT-SGOOD-DEF`" is then realized *as the derived edge from this
node*, not as a bare edge.

Why the other two options misstate the mathematics:

- **Reuse `FLT-CLASS-FIELD` (line 17).** It is `target_stage: T2`, owns "reciprocity, induced
  characters, local prescriptions" (`classField_package`). Folding the tame character here would
  (i) drag an elementary, pre-1980s fact to T2; (ii) place **full reciprocity on the immediate MLT
  path** — the exact hidden-reciprocity assumption the stop-loss forbids; (iii) create a false edge
  `FLT-CLASS-FIELD → FLT-SGOOD-DEF` claiming S-good's trace condition needs class field theory. This
  recreates the rejected omnibus `classField_package`.
- **Reuse `FLT-SGOOD-DEF` (line 6).** Its `current_state` is **`proved`** (the four-field
  `BlueprintSGood` structure elaborates); its `source_condition_risks` already records the tame TODO
  as *a dependency caveat, not a defect in the four-field signature*. Folding the open kernel theorem
  into a `proved` node re-opens it and conflates the S-good **structure** (done) with the tame-kernel
  **characterization** (open). It also cannot serve the `cyclic_base_change`/`hρtame` consumer, which
  lives in the automorphic cluster and never routes through `BlueprintSGood`.
- **Add a direct edge only.** Edges in this system are **derived** from each node's
  `direct_dependencies` (`generate_graph.py:82–94`); a bare edge is not a first-class object and can
  carry no `source_refs`, `completion_gate`, `target_stage`, or `kernel_probe_state`. The TODO would
  remain an untracked gap and the Serre source-locator gate would have nowhere to live.

Only a standalone node is both T1 and off-reciprocity while owning the symbol for **both** clusters
(SGood and automorphic). That is the minimal faithful repair.

---

## §2 — Exact Lean declarations (replace the canonical-kernel TODO; keep full vs tame distinct)

**Principle: purely additive.** Do **not** change the existing `def localTameAbelianInertiaGroup`
(its proxy carrier typechecks and its `Subgroup` proofs are complete, no `sorry`). The TODO is
discharged by *proving* a characterization theorem, so the three consumers need **zero** signature
changes.

Add, in the same top-level scope in `AbsoluteGaloisGroup.lean` (context: `{K} [Field K] [NumberField K]`,
`v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, `Γ Kᵥ = Field.absoluteGaloisGroup Kᵥ`,
`κ 𝒪ᵥ = IsLocalRing.ResidueField 𝒪ᵥ`):

```lean
/-- Elementary tame residue character on full inertia (Kummer/Serre, GTM 67 Ch. IV §2).
    NO local class field theory: built from p-1 roots of the uniformiser in Kᵘʳ. -/
noncomputable def tameResidueChar (v : Ω K) : localInertiaGroup v →* (κ 𝒪ᵥ)ˣ := ...   -- GOAL

/-- Tame abelian inertia is contained in full inertia. First genuine goal (see §5). -/
theorem localTameAbelianInertiaGroup_le_localInertiaGroup (v : Ω K) :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v := ...                        -- GOAL

/-- The canonical-kernel theorem discharging the TODO@176: the proxy carrier is exactly
    the kernel of the tame residue character (mapped back into Γ Kᵥ). -/
theorem localTameAbelianInertiaGroup_eq_ker (v : Ω K) :
    localTameAbelianInertiaGroup v
      = (tameResidueChar v).ker.map (localInertiaGroup v).subtype := ...               -- GOAL
```

Distinction preserved at the type level:

- **Full inertia** `localInertiaGroup v : Subgroup (Γ Kᵥ)` (`AbsoluteGaloisGroup.lean:167`) — keeps
  its sole consumer `narrowTraceConditionFunctor` (`LiftFunctor.lean:139`).
- **Tame abelian inertia** `localTameAbelianInertiaGroup v : Subgroup (Γ Kᵥ)`
  (`AbsoluteGaloisGroup.lean:178`) — the *kernel* of `tameResidueChar`, keeps the three tame
  consumers. The relation is a `≤`, **never** an `=` (wild inertia is excluded).

These three declarations are the entire mathematical content the new obligation owns. Do not redefine
`localTameAbelianInertiaGroup` as `.ker.map …` (would break consumer defeq); prove equality instead.

---

## §3 — Exact graph edges and target stage (reciprocity is NOT upstream)

New node record fields (set `direct_dependencies`; let `generate_graph.py` derive edges/depth/SCC —
never hand-edit `proof-graph.ndjson` / `flt-proof-program.instances.json`):

- `obligation_id: FLT-TAME-RESIDUE`, `target_stage: T1`, `completion_targets: ["T1","T2","T3"]`,
  `current_state: definition-gap`, `mathematical_novelty: standard`, `lean_risk: low`.
- `lean_declaration: tameResidueChar, localTameAbelianInertiaGroup_eq_ker`.
- `direct_dependencies:` **`[]`** upstream (elementary; no reciprocity, no CFT). If the register
  confirms `localInertiaGroup` is *owned* by `FLT-LOCAL-GALOIS` (owner FLT-402), then
  `["FLT-LOCAL-GALOIS"]` is admissible; otherwise `[]`. **Confirm before setting — do not fabricate.**
- `library_candidates: ["localInertiaGroup","IsLocalRing.ResidueField","Subgroup.map"]` (all real).

Downstream edges (add `FLT-TAME-RESIDUE` to each consumer-owner's `direct_dependencies`):

- `FLT-SGOOD-DEF` (owns `BlueprintSGood.traceOnJ`) → derives `E-TAME-RESIDUE-SGOOD-DEF`. **This is the
  exact tame-kernel edge stage-7 demanded.**
- `FLT-SGOOD-SELECTED` (owns the "tame rank-one quotient at S", i.e. `cyclic_base_change`/`hρtame`) →
  derives `E-TAME-RESIDUE-SGOOD-SELECTED`.
- The obligation owning `traceConditionFunctor` (deformation cluster, `LiftFunctor.lean:129`) → **owner
  id to be confirmed in review; do not guess.**

Deliberately absent (guard, from stage-6 lines 137–140):

- `FLT-CLASS-FIELD → FLT-TAME-RESIDUE` — ABSENT. Reciprocity is **not** upstream: `tameResidueChar` is
  constructed by elementary Kummer theory (roots of the uniformiser in `Kᵘʳ`), matching the existing
  doc-comment at `AbsoluteGaloisGroup.lean:171–174`. Stage-6 recorded that putting reciprocity
  upstream was "Stage 1 backwards."
- `T-LOCAL-RECIP → FLT-TAME-RESIDUE` — ABSENT.
- `FLT-CLASS-FIELD` keeps only its two existing out-edges (`E-CLASS-FIELD-INDUCED-MOD`,
  `E-CLASS-FIELD-AUX-CURVE`). Global reciprocity stays isolated in the gated `T-GLOBAL-RECIP`/`T2b`.

Stage: **T1** ("sorry-free modulo 1980s"). The tame character is classical (Serre 1962), so T1's
`knownin1980s` policy covers it; T2/T3 promotion additionally requires the source-locator row (§4).

---

## §4 — Source ownership and the exact source-locator gate (no fabricated proposition numbers)

- **Owner:** local-Galois work-item (`FLT-402` neighbourhood, which owns `localInertiaGroup`), **not**
  `FLT-AUX-LOCAL-FIELD` (owner FLT-413). Skinner–Wiles CFT trick stays routed to
  `FLT-AUX-LOCAL-FIELD` per stop-loss S4 ("solvable-field work stays in FLT-AUX-LOCAL-FIELD"). The
  tame residue character is not auxiliary-field material.
- **Source:** candidate is Serre, *Local Fields* (GTM 67), Ch. IV §2 (tame character). The register
  (`SOURCE-REGISTER.md`, SRC-001…SRC-025) currently holds **no** CFT/tame primary source.
- **Locator gate (anti-fabrication):** add at most a new row (next free id, e.g. SRC-026) whose
  `Locator` is left as the chapter/section only and whose `Verification state` is the truthful
  caveat, e.g. *"Primary source identified; exact §/Proposition and printed page not yet visually
  checked; Lean statement absent."* **Do NOT write a proposition or page number that has not been
  visually checked.** `HIST-UNRESOLVED` forbids any T2 assumption "until an exact Lean type **and**
  primary-source locator have been independently reviewed" — so `FLT-TAME-RESIDUE` may build
  kernel-clean at **T1** but **cannot be promoted past T1** until that Serre row's exact locator is
  visually checked and reviewed. `source_refs` for the node: `["SRC-004"]` now (blueprint), plus the
  new Serre row once its state is recorded — never a fabricated locator.

---

## §5 — Smallest no-axiom probe buildable now, and the first genuine goal

**Probe (buildable now, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):**
`FLTMethodology/Probes/TameResidueBoundary.lean` — **audit-only, no theorem/lemma/axiom/sorry**,
mirroring the stage-8 idele probe. It contains only:

- `#check` of the three consumer signatures (`BlueprintSGood.traceOnJ`, `traceConditionFunctor`,
  `cyclic_base_change`) and of `localInertiaGroup`, `localTameAbelianInertiaGroup`.
- `#print axioms localTameAbelianInertiaGroup`, `#print axioms localInertiaGroup`,
  `#print axioms BlueprintSGood` — confirming the def-layer is already kernel-clean (the TODO is a
  *math* gap, not a `sorry`).
- Asserts **nothing** about the kernel theorem, containment, reciprocity, or the character (all
  unproved). The warm-up containment lemma is NOT in the probe (it would need a proof/`sorry`).

**First genuine mathematical goal:** prove
`localTameAbelianInertiaGroup_le_localInertiaGroup` (containment). The current proxy carrier is
quantified over all of `Γ Kᵥ` and is not even syntactically inside inertia, so containment is the
first real content and a prerequisite to `localTameAbelianInertiaGroup_eq_ker`. Order:
containment → `tameResidueChar` construction → kernel theorem.

---

## §6 — Migration / consumer steps (all zero-signature)

Because the repair is additive, **no consumer signature changes**:

- `BlueprintSGood.traceOnJ` (`Conditions.lean:40`, `∀ σ ∈ localTameAbelianInertiaGroup v, trace = 2`)
  — unchanged; semantic content justified once the kernel theorem lands. Add `FLT-TAME-RESIDUE` to
  `FLT-SGOOD-DEF.direct_dependencies` only.
- `traceConditionFunctor` (`LiftFunctor.lean:129`, same tame condition) — unchanged. **Keep
  `narrowTraceConditionFunctor` (`LiftFunctor.lean:139`) on `localInertiaGroup`** — do NOT switch it to
  tame (full-inertia consumer; see CE-A). Add `FLT-TAME-RESIDUE` to its owner's dependencies.
- `cyclic_base_change` / `hρtame` (`Automorphic.lean:186`, `localTameAbelianInertiaGroup w ≤ δ.ker`)
  — hypothesis unchanged. The `sorry` at `Automorphic.lean:194` is a **separate** obligation
  (`FLT-SGOOD-SELECTED` / cyclic base change), NOT discharged here. Add `FLT-TAME-RESIDUE` to that
  obligation's dependencies.

This is the smallest migration: three dependency-set insertions, one new node, one probe, three Lean
goals — no edit to any consumer type.

---

## §7 — Counterexamples and stop-losses

- **CE-A (full-inertia / tame conflation).** Trace-2-on-tame is strictly weaker than
  trace-2-on-full-inertia; `localTameAbelianInertiaGroup v ⊊ localInertiaGroup v` in general (wild
  inertia excluded). *Stop-loss:* keep the two symbols distinct; the relating lemma is a `≤`, never an
  `=`; never retarget `narrowTraceConditionFunctor`.
- **CE-B (hidden reciprocity).** Building `tameResidueChar` via `IsLocalClassField`/a reciprocity map
  puts `FLT-CLASS-FIELD` (T2) upstream of a T1 node and smuggles reciprocity onto the MLT path.
  *Stop-loss:* construct via elementary Kummer roots of the uniformiser in `Kᵘʳ`; forbid any edge from
  `FLT-CLASS-FIELD` or `T-LOCAL-RECIP` into `FLT-TAME-RESIDUE`. If a proof genuinely needs
  reciprocity → STOP, return `REVISE`.
- **CE-C (generic class-field package).** Folding tame residue into `classField_package` recreates the
  rejected omnibus and drags an elementary T1 fact to T2. *Stop-loss:* `FLT-TAME-RESIDUE` stays a
  standalone T1 node; `FLT-CLASS-FIELD` keeps exactly its two existing out-edges; its
  `library_candidates` overclaim (`IsLocalClassField`, `ContinuousCharacter` don't exist at this SHA)
  is a *separate* cleanup, not part of this boundary.
- **CE-D (direction / inversion — stage-6 CE-7).** No live consumer distinguishes `t_v` from `t_v⁻¹`
  (all use `∈` / `≤ ker`, inversion-stable). *Stop-loss:* record the character's orientation as a
  convention, not a compile-gating theorem; do not assert a reciprocity-normalized direction absent
  `T-LOCAL-RECIP`.
- **CE-E (proxy treated as kernel).** Treating the current TODO carrier as already the kernel.
  *Stop-loss:* the node stays `definition-gap` until `localTameAbelianInertiaGroup_eq_ker` is proved
  and axiom-audited. The def is NOT mathematically discharged today.
- **Source stop-loss.** No SRC row may state an exact Serre proposition/page number until visually
  checked; until then `FLT-TAME-RESIDUE` cannot be promoted past T1.

---

## Verification (how the eventual edit would be checked)

1. `lake build FLTMethodology.Probes.TameResidueBoundary` green; every `#print axioms` exactly
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
2. `lake build FLTMethodology` stays green (no regression to the frozen idele tranche).
3. `python methodology/control/generate_graph.py` regenerates edges/depth/SCC with no cycle and no
   unknown-dependency error; confirm `E-TAME-RESIDUE-SGOOD-DEF` appears and no
   `FLT-CLASS-FIELD → FLT-TAME-RESIDUE` edge exists.
4. After the math lands: `#print axioms localTameAbelianInertiaGroup_eq_ker` audited at the node's
   target stage.

## Open items for GPT review (flagged, not fabricated)

- Confirm the obligation that owns `traceConditionFunctor` (deformation cluster) before adding its
  dependency edge.
- Confirm whether `localInertiaGroup` ownership warrants `FLT-TAME-RESIDUE.direct_dependencies =
  ["FLT-LOCAL-GALOIS"]` vs `[]`.
- Confirm SRC id (SRC-026) and truthful Verification-state wording for the Serre row.

**Verdict: `READY-FOR-GPT-REVIEW`.**
