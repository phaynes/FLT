# Stage 12 — Fable 5 tame-residue diversity repair (independent corrected design)

**Verdict: `DESIGN-VIABLE`** (independent design; not an edit of the Opus stage-10 artifact).
Read-only pass. No Lean, control, graph, source, review, or task file was edited. Temporary
probes ran from `/tmp` against the pinned `.olean`s and were deleted. No graph mutation, source
registration, axiom registration, or proof-completion claim is made or authorized here.

## Context

The class-field pipeline isolated one definition gap on the live MLT critical path: the repository
symbol `localTameAbelianInertiaGroup` (`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:178`,
TODO at line 176) is a proxy carrier for `J_v = ker(I_v → k(v)ˣ)` with an unproved canonical-kernel
characterization. Stage-10 (Opus) proposed a standalone T1 obligation `FLT-TAME-RESIDUE`; stage-11
(GPT-5.6 xhigh) returned `REVISE — substantive` with corrections (wild inertia misstatement, consumer
misassignment, missing closedness prerequisite). Difficulty 10 + substantive revision triggers this
required Fable diversity pass. This document is the corrected independent design for later Opus
synthesis.

---

## 1. T1 `FLT-TAME-RESIDUE` ownership — INDEPENDENTLY VERIFIED

A standalone T1 obligation is correct. Independent evidence from the current register
(`methodology/control/proof-obligations.ndjson`, 52 records):

- The id is free: no record contains `TAME`, `RESIDUE`, or `INERTIA`; **no obligation names
  `localInertiaGroup`, `localTameAbelianInertiaGroup`, or `traceConditionFunctor` at all** (grep: 0
  hits) — the symbols are currently unowned.
- Reuse of `FLT-CLASS-FIELD` is wrong: it is `target_stage: T2`, `current_state: definition-gap`,
  `direct_dependencies: []`, owning `classField_package`. Folding an elementary pre-1980s fact there
  drags it to T2 and puts reciprocity on the MLT path — exactly the forbidden hidden-reciprocity
  route.
- Reuse of `FLT-SGOOD-DEF` is wrong: it is `current_state: proved` and its
  `source_condition_risks` already records the tame TODO as an upstream caveat, not a defect of the
  four-field signature. Folding the open kernel theorem in would re-open a proved node, and it cannot
  serve `cyclic_base_change` (automorphic cluster, never routes through `BlueprintSGood`).
- A bare edge is impossible: `generate_graph.py` derives every edge from `direct_dependencies`
  (verified at lines 73–95 of the current file); edges are not first-class and carry no gate, stage,
  or source refs. `proof-graph.ndjson` is generated output and must never be hand-edited.

**Decision: add `FLT-TAME-RESIDUE`, `target_stage: T1`, standalone, off the reciprocity path.**

## 2. The exact distinction `P_v ≤ J_v ≤ I_v`

Let `I_v = localInertiaGroup v`, `J_v = localTameAbelianInertiaGroup v`, `P_v` wild inertia
(no Lean symbol exists in the pin — grep for `wildInertia`/`WildInertia`: 0 hits, so `P_v` appears
in commentary only, never as a Lean claim).

- `J_v = ker(t_v : I_v → k(v)ˣ)`. Since `k(v)ˣ` has order `q − 1` prime to `p = char k(v)`, the
  pro-`p` group `P_v` maps trivially, so **`P_v ≤ J_v`**. Wild inertia is NOT excluded from `J_v`
  (stage-10's contrary claim is refuted; stage-11's correction is confirmed).
- **`J_v ≤ I_v`** is the only subgroup relation to be proved in Lean, and it is a `≤`, never `=`.
- **No universal strictness.** Witness inside the pin's own definition: if `k(v) = 𝔽₂` then
  `Nat.card (κ 𝒪ᵥ) − 1 = 1`, the carrier condition degenerates to
  `∀ x, x ∈ fixedField I_v → σ x = x`, i.e. `J_v = fixingSubgroup (fixedField I_v) = I_v`
  (using closedness, §5). So `J_v < I_v` fails at every place of residue field `𝔽₂`.
- `narrowTraceConditionFunctor` (`LiftFunctor.lean:138`) stays on full inertia `I_v`; it is never
  retargeted.

## 3. Downstream edges verified; no upstream or reciprocity edge required

**Four consumer-owner insertions (add `FLT-TAME-RESIDUE` to `direct_dependencies` of):**

| Owner | Live consumer verified in pin | Notes |
|---|---|---|
| `FLT-SGOOD-DEF` | `BlueprintSGood.traceOnJ` (`Conditions.lean:40`) | the exact tame-kernel edge stage-7 demanded |
| `FLT-SUPPORT-DEFORMATION` | `Deformation.traceConditionFunctor` (`LiftFunctor.lean:128`) | its record owns "lift-functor declarations in FLT/Deformations"; no other record covers the file |
| `FLT-SGOOD-SELECTED` | prospective `SelectedGood` "tame rank-one quotient at S" (in its `lean_type`) | direct symbol mention in the future signature |
| `FLT-CBASE` | `cyclic_base_change` hypothesis `hρtame` (`Automorphic.lean:186`: `localTameAbelianInertiaGroup w ≤ δ.ker`) | `FLT-CBASE.lean_declaration` is exactly `cyclic_base_change`; stage-11's reassignment away from SGOOD-SELECTED-only is confirmed |

Derived edges (generated, `edge_kind: theorem` since `FLT-TAME-RESIDUE` is not in the hardcoded
`definition_obligations` set — synthesis must either accept `theorem` kind or add the id to that
set in `generate_graph.py`; flagging, not deciding):
`E-TAME-RESIDUE-SGOOD-DEF`, `E-TAME-RESIDUE-SUPPORT-DEFORMATION`, `E-TAME-RESIDUE-SGOOD-SELECTED`,
`E-TAME-RESIDUE-CBASE`.

**Transitively reduced graph.** With current deps (`FLT-SGOOD-SELECTED.deps ⊇ {FLT-SGOOD-DEF}`,
`FLT-SUPPORT-DEFORMATION.deps = []`, `FLT-CBASE.deps = [FLT-AUT-DEF]`, `FLT-AUT-DEF.deps = []`):

```
FLT-TAME-RESIDUE ──→ FLT-SGOOD-DEF ──→ FLT-SGOOD-SELECTED
        ├──────────→ FLT-SUPPORT-DEFORMATION
        └──────────→ FLT-CBASE
```

The reduction drops `FLT-TAME-RESIDUE → FLT-SGOOD-SELECTED` (implied via `FLT-SGOOD-DEF`). The
raw record nevertheless keeps all four insertions because this graph's edge semantics is *direct
symbol consumption* (the `SelectedGood` signature will itself name the subgroup), and
`generate_graph.py` performs no reduction. Both facts must be stated; neither may be silently
collapsed into the other.

**No upstream dependency** (`direct_dependencies: []`), proved three ways:
1. Register: no obligation owns `localInertiaGroup` or the `AbsoluteGaloisGroup` module (0 grep hits).
2. Lean: the two new theorems already close using only Mathlib + `FLT.Mathlib` instances — probe
   axioms exactly `[propext, Classical.choice, Quot.sound]` (§5), so no obligation-owned Lean is in
   the dependency closure.
3. Cycle obstruction: `FLT-LOCAL-GALOIS` upstream would create the cycle
   `LOCAL-GALOIS → TAME-RESIDUE → SGOOD-DEF → SGOOD-SELECTED → LOCAL-GALOIS` (and a second cycle
   through `SUPPORT-DEFORMATION → DEF-FUNCTOR → LOCAL-GALOIS`), since
   `FLT-LOCAL-GALOIS.deps = [FLT-SGOOD-SELECTED, FLT-DEF-FUNCTOR]`. Stage-11's prohibition is
   confirmed and strengthened (two distinct cycles, not one).

**No reciprocity edge:** no `IsLocalClassField` / `LocalClassField` / `localReciprocity` symbol
exists in the pin (grep: 0 hits); the construction plan (§7) consumes only alg-closed root
existence, separability of `X^{q−1} − 1` over `k(v)` (`gcd(q−1, p) = 1`), and Hensel-type root
lifting. Edges from `FLT-CLASS-FIELD` or any reciprocity node: ABSENT, forbidden.

## 4. Temporary-probe results (exact signatures)

Probe files lived in `/tmp/flt-tame-probe-s12/` (deleted), run with `lake env lean` against the
current pinned `.olean`s (toolchain `leanprover/lean4:v4.32.0-rc1`; `.olean` newer than source, so
the cache is fresh). Context: `{K} [Field K] [NumberField K]`, `v : HeightOneSpectrum (𝓞 K)`,
`Γ`/`Kᵥ`/`𝒪ᵥ`/`κ` as in `AbsoluteGaloisGroup.lean`.

All four target signatures elaborate (Probe 1, `sorry`-bodied, warnings only):

```lean
noncomputable def tameResidueChar : localInertiaGroup v →* (κ 𝒪ᵥ)ˣ

theorem localTameAbelianInertiaGroup_le_localInertiaGroup :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v

theorem localTameAbelianInertiaGroup_eq_ker :
    localTameAbelianInertiaGroup v
      = (tameResidueChar v).ker.map (localInertiaGroup v).subtype

theorem isClosed_localInertiaGroup :
    IsClosed (localInertiaGroup v : Set (Γ Kᵥ))
```

- `#synth TopologicalSpace (κ 𝒪ᵥ)ˣ` **fails** — the continuous-hom variant
  `localInertiaGroup v →ₜ* (κ 𝒪ᵥ)ˣ` cannot elaborate; the plain `→*` is the correct minimal
  current type (stage-11 confirmed).
- Instance audit (Probe 2): `#synth ContinuousSMulDiscrete (Γ Kᵥ) (Kᵥᵃˡᵍ)` →
  `instContinuousSMulDiscreteAlgEquivOfIsAlgebraic`;
  `#synth ContinuousSMulDiscrete (Γ Kᵥ) (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))` →
  `continuousSMulDiscrete_integralClosure`; `#synth IsGalois Kᵥ (Kᵥᵃˡᵍ)` → `IsSepClosure.isGalois`.

## 5. Smallest proof of `isClosed_localInertiaGroup` — CLOSES IN THIS PIN

Route: **closed ideal-inertia**, not a continuous residue action and not a closed-fixing-subgroup
theorem. The one missing lemma is general and Mathlib-shaped; probe 2 proved it in full:

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
    rw [this]
    exact isOpen_biUnion fun y _ ↦ ContinuousSMulDiscrete.isOpen_smul_eq G x y
  rw [show {σ : G | σ • x - x ∈ I} = {σ : G | σ • x ∈ {y | y - x ∈ I}} from rfl,
    ← isOpen_compl_iff]
  exact hopen {y | y - x ∈ I}ᶜ

theorem isClosed_localInertiaGroup : IsClosed (localInertiaGroup v : Set (Γ Kᵥ)) :=
  AddSubgroup.isClosed_inertia _ _
```

`#print axioms` for both: exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
No `IsClosed`-of-inertia lemma exists anywhere in the pin (grep over Mathlib + FLT: 0 hits), so
`AddSubgroup.isClosed_inertia` is the exact missing lemma — and it is *provable now*, not an open
residual. **This corrects stage-11**, which listed closedness as the "first actual Lean residual":
closedness is a ~12-line buildable unit, because `continuousSMulDiscrete_integralClosure` and the
algebraic-extension `ContinuousSMulDiscrete` instance already exist in the pin.

## 6. Containment with closedness supplied — no residual inside containment

Probe 2 proof, closing completely (axioms: standard trio):

```lean
theorem localTameAbelianInertiaGroup_le_localInertiaGroup :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v := by
  intro σ hσ
  have hfix : σ ∈ (IntermediateField.fixedField (localInertiaGroup v)).fixingSubgroup := by
    rintro ⟨x, hx⟩
    exact hσ x (pow_mem hx _)
  rwa [InfiniteGalois.fixingSubgroup_fixedField
    ⟨localInertiaGroup v, isClosed_localInertiaGroup v⟩] at hfix
```

Residuals **after** containment (the complete list; none belongs to containment itself):

- **R1 (first expected Lean residual going forward):** the reduction isomorphism on tame roots of
  unity — injectivity of `μ_{q−1}(integral closure) → μ_{q−1}(residue field)` and the
  identification `μ_{q−1}(κ̄) = k(v)ˣ` (uses separability of `X^{q−1} − 1` mod `𝔪`, valid since
  `gcd(q−1, p) = 1`). No such lemma exists in the pin.
- **R2:** construction of `tameResidueChar` itself: chosen uniformiser `ϖ`, chosen root
  `x` of `X^{q−1} − ϖ` in `Kᵥᵃˡᵍ`, well-definedness in the root choice, multiplicativity
  (both reduce to R1 plus `σζ = ζ` for `σ ∈ I_v`, `ζ ∈ μ_{q−1}`).
- **R3 (deepest):** the kernel theorem's hard inclusion `ker t_v ≤ J_v`, which needs
  "(q−1)-th roots of units exist in `fixedField (localInertiaGroup v)`" — a Hensel-type lifting in
  the Henselian (non-complete) valuation ring of the maximal unramified subextension, plus
  valuation bookkeeping `y = ζ · u^{1/(q−1)} · xⁿ`. The easy inclusion `J_v ≤ ker t_v ∘ map` uses
  only `ϖ ∈ Kᵥ ⊆ fixedField I_v`.

R3 justifies stage-11's `lean_risk: high` upgrade over stage-10's `low`; the demonstrated
closedness+containment prefix is low-risk, the character/kernel tranche is not.

## 7. Source-faithful elementary construction plan (no reciprocity)

For `σ ∈ I_v`: fix a uniformiser `ϖ` of `Kᵥ` and a root `x` of `X^{q−1} = ϖ` in `Kᵥᵃˡᵍ`
(`q = Nat.card (κ 𝒪ᵥ)`). Then `(σx/x)^{q−1} = σ(ϖ)/ϖ = 1`, so `σx/x ∈ μ_{q−1}`; define
`t_v(σ) :=` residue of `σx/x`, valued in `k(v)ˣ` via R1. Multiplicativity and root-independence
follow from: `σ ∈ I_v` fixes each `ζ ∈ μ_{q−1}` (σζ and ζ are `(q−1)`-roots of unity with equal
residues; injectivity R1 forces equality). Kernel characterization per §6 R3. Inputs: alg-closed
root existence, separability of `X^{q−1} − 1` over `k(v)`, Henselian root lifting. **At no point**
a reciprocity map, `classField_package`, idele, or Frobenius normalization. Orientation of `t_v`
vs `t_v⁻¹` is recorded as a convention (all live consumers use `∈`/`≤ ker`, inversion-stable) —
no reciprocity-normalized direction may be asserted (stage-6 CE-7 preserved).

## 8. Source locator gate (kept closed)

`methodology/SOURCE-REGISTER.md` holds SRC-001…SRC-025; **no** Serre *Local Fields* row exists.
Gate, unchanged from stage-11: do **not** add `SRC-026`; do **not** write any Serre proposition,
section, or page number (none has been visually checked in this pipeline); node
`source_refs: ["SRC-004"]` only (blueprint sketch, honestly recorded as incomplete). Promotion past
T1 is blocked until a primary locator is visually verified and independently reviewed. No T2
historical assumption is authorized; despite T1's global `knownin1980s` allowance, this node's own
completion gate requires the standard axiom trio only.

## 9. Audit-only probe classification

Probe 3 (`#check`/`#print axioms` only, no theorem/lemma/axiom/sorry) is **signature evidence
only** — it demonstrates that the consumer signatures elaborate and what axioms the *definition
layer* uses; it discharges no mathematics and must be recorded as
`kernel_probe_state: signature-green`, never as progress on the TODO. Results:
`localInertiaGroup`, `localTameAbelianInertiaGroup`, `BlueprintSGood`, `traceConditionFunctor`,
`narrowTraceConditionFunctor` → exactly `[propext, Classical.choice, Quot.sound]`;
`cyclic_base_change` → `[propext, sorryAx, Classical.choice, Quot.sound]` (separately owned by
`FLT-CBASE`; not touched by this repair).

## 10. Deliverable for Opus synthesis

**Candidate obligation row** (mutation NOT applied here):

```text
obligation_id: FLT-TAME-RESIDUE
mathematical_name: Tame residue character and canonical kernel at a finite place
lean_declaration: AddSubgroup.isClosed_inertia, isClosed_localInertiaGroup,
  localTameAbelianInertiaGroup_le_localInertiaGroup, tameResidueChar,
  localTameAbelianInertiaGroup_eq_ker
target_stage: T1
completion_targets: [T1, T2, T3]
current_state: definition-gap
direct_dependencies: []
source_refs: [SRC-004]
critical_path: true
mathematical_novelty: standard
lean_risk: high            # per §6 R3; the closedness/containment prefix is demonstrated low
expected_module: FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
kernel_probe_state: signature-green
completion_gate: closedness, containment, tameResidueChar, and the kernel theorem compile;
  every new theorem audits to exactly [propext, Classical.choice, Quot.sound]; consumer
  signatures unchanged; graph regeneration yields exactly the four derived edges, no cycle,
  no reciprocity edge; primary-source locator visually checked before any promotion past T1.
```

**Four dependency mutations:** append `"FLT-TAME-RESIDUE"` to `direct_dependencies` of
`FLT-SGOOD-DEF`, `FLT-SUPPORT-DEFORMATION`, `FLT-SGOOD-SELECTED`, `FLT-CBASE`; regenerate via
`generate_graph.py` (never hand-edit `proof-graph.ndjson`). Note §3's edge-kind and
transitive-reduction flags.

**Bounded Lean units (in order):**
- **U1 — first buildable unit:** `AddSubgroup.isClosed_inertia` + `isClosed_localInertiaGroup`
  (~15 LOC, proof text in §5, closes today, standard trio).
- **U2 — first genuine theorem:** `localTameAbelianInertiaGroup_le_localInertiaGroup`
  (~8 LOC, proof text in §6, closes today given U1).
- **U3:** μ_{q−1} reduction injectivity + `μ_{q−1}(κ̄) ≃ k(v)ˣ` (**first expected Lean residual**).
- **U4:** `tameResidueChar` definition + `MonoidHom` proof (needs U3).
- **U5:** unit-root Hensel lemma in `fixedField (localInertiaGroup v)` (R3).
- **U6:** `localTameAbelianInertiaGroup_eq_ker` (needs U3–U5); discharges the TODO@176.
- Audit-only probe file `FLTMethodology/Probes/TameResidueBoundary.lean` may accompany U1
  (signature evidence only, §9).

All units are **purely additive**: `localTameAbelianInertiaGroup` is never redefined (consumer
defeq preserved), zero consumer signature changes.

**Stop-losses:**
- S1: any proof requiring a reciprocity map, `classField_package`, or an edge from
  `FLT-CLASS-FIELD`/local-global reciprocity → STOP, return `REVISE`.
- S2: any `=` between `J_v` and `I_v`, any universal strictness claim, any "wild inertia excluded"
  claim, or any Lean statement about `P_v` (no symbol exists) → STOP.
- S3: retargeting `narrowTraceConditionFunctor` to the tame subgroup → STOP.
- S4: any SRC row with an unverified Serre locator, or any promotion past T1 before visual
  verification → STOP.
- S5: any new theorem auditing beyond `[propext, Classical.choice, Quot.sound]`, or treating the
  probe/proxy as mathematical discharge → STOP; node stays `definition-gap` until U6 lands.
- S6: U5 exceeding ~300 LOC or requiring completed-field machinery not in the pin → pause and
  re-review rather than importing new analytic infrastructure.

## Verification (for the eventual edit, not this pass)

1. `lake env lean` on the new declarations; `#print axioms` = standard trio for each unit landed.
2. `lake build FLTMethodology` stays green (frozen idele tranche untouched).
3. `python methodology/control/generate_graph.py`: four derived `E-TAME-RESIDUE-*` edges, no
   cycle, no `FLT-CLASS-FIELD → FLT-TAME-RESIDUE` edge.
4. Consumer files byte-identical.

**Verdict: `DESIGN-VIABLE`.**
