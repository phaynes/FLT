# Stage 4 — Opus bounded build review: Moret–Bailly adapters

## Context

This is a **read-only review**, not an implementation task. Stage 4 audits two newly persisted
bounded Lean units for the Moret–Bailly obligation and returns a verdict. The review cannot
authorize an axiom, change `HIST-UNRESOLVED`, or promote the obligation from `absent`. No
repository files, control rows, task state, or Lean sources were edited. Builds and `#print axioms`
probes touch only the `.lake/build` cache (read-only w.r.t. tracked source), which the prompt
designates as the final authority.

Repo root: `/Volumes/second-store/devel/proof-forks/FLT` — toolchain `leanprover/lean4:v4.32.0-rc1`,
git-clean (only untracked `.kg-model-bridge/`).

## Verdict: **PASS**

### 1. Exact axiom surface — CONFIRMED `[propext, Classical.choice, Quot.sound]`

Verified twice per declaration (direct `lake env lean` elaboration + full `lake build` replay,
8984 jobs, "Build completed successfully"). No `sorryAx`, no extra axioms.

- `FLT.PotentialModularity.linearDisjoint_of_compositum` → `[propext, Classical.choice, Quot.sound]`
- `AlgebraicGeometry.Scheme.ptsOver` → `[propext, Classical.choice, Quot.sound]`
- `FLT.PotentialModularity.MoretBailly.ptsMap` → `[propext, Classical.choice, Quot.sound]`

### 2. Variance & base compatibility — CONFIRMED

- `linearDisjoint_of_compositum` (theorem, `MoretBaillyFieldAdapters.lean:16`): from
  `L.LinearDisjoint (K₁ ⊔ K₂)` derives `L.LinearDisjoint K₁ ∧ L.LinearDisjoint K₂` via
  `IntermediateField.LinearDisjoint.of_le_right` + `le_sup_left/right`. Faithful to statement.
- `ptsOver` (def, `MoretBaillyLocalPointsAlgebraic.lean:18`, injected into
  `AlgebraicGeometry.Scheme` via `_root_.` — NOT upstream Mathlib): subtype of `Spec R ⟶ X`
  morphisms lying over the `Spec K` base point. Purely Spec-level/algebraic; no topology.
- `ptsMap` (noncomputable def, `:27`): `(φ : R →ₐ[K] S) : X.ptsOver K R → X.ptsOver K S` —
  **covariant** in the algebra argument (R→S; contravariant geometrically via `Spec.map φ`
  precomposition). Base compatibility discharged by `φ.commutes` (the `→ₐ[K]` fixing of `K`),
  exactly as claimed.

### 3. Control-plane honesty — CONFIRMED (not misdescribed)

The prompt's four misdescription risks are all absent:
- **Not a topology**: `source_condition_risks` explicitly records the v-adic topology + source-topology
  comparison as *absent*; `kernel_probe_state:"algebraic-boundary-proof-green"`.
- **Not the source theorem**: `primary_source_exact:false`, `hypothesis_translation:false`,
  `lean_signature:false`; `moret_bailly_point` still labelled "Proposed".
- **Not a T2 boundary**: `current_state:"absent"`, `review_state:"source-contract-repair-required"`;
  notes state "The adapters do not authorize T2" / "no T2 registration ... implied";
  `HIST-UNRESOLVED` stays `status:"unresolved"`.
- **Not a proof of FLT-MORET-BAILLY**: `promotion_allowed:false`; obligation `absent`; MISS-005
  `verdict:"absent"`.

Probe docstrings self-disclaim ("does not state or assume the Moret–Bailly existence theorem";
"deliberately supplies no topology ... no local-open comparison ... no existence theorem").
Stage-3 GPT review (REVISE-substantive for the larger tranche) explicitly *accepted these two
smaller units* as kernel-clean.

Minor observation (non-blocking, pre-existing, out of this tranche's scope): `component-bom.ndjson:16`
carries `coverage:"exact"` — but this is a *planned binding* field (target_stage T2, owner FLT-303),
not a coverage/proof assertion about the adapters; every state-bearing row keeps the obligation
absent. Not a misdescription of the adapters.

### Residual goals (open; NOT established by these adapters)

- Canonical v-adic topology on `X.ptsOver K K_v` and its agreement with the source's local topology.
- Meaning of the local `open` conditions (source-topology comparison) — cannot be deferred.
- Affine-chart domain gap (`X.Over (Spec K)` does not supply `Algebra K Γ(X,U)`) and `ptsEquiv`
  inverse continuity (from Stage-3 adjudication).
- Exact source contract selection: MB89 Thm 1.3 (+ proved Galois/disjointness/project adapters) vs
  the later BLGGT Proposition 3.1.1 modern boundary.
- Galoisness and avoidance-field linear disjointness of the produced global field.
- The `moret_bailly_point` existence theorem itself.

### Authority boundary

This PASS accepts only the three bounded algebraic adapters as kernel-clean. It does **not** authorize
any axiom, does **not** change `HIST-UNRESOLVED`, and does **not** promote `FLT-MORET-BAILLY` from
`absent`. No repository edits are proposed or authorized.
