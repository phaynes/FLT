# Stage 1 primary design — Opus 4.8

## Model and transport evidence

- Agent: `opus48-primary-designer-d10`
- Configured model: `claude-opus-4-8`
- Backend transport: `claude-code`
- Role: `primary`
- Difficulty: `10/10`
- Scheduled design budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `790798 ms`
- Claude session: `8693c526-59f4-41dc-9450-8fd4c8e272b1`
- Token audit: `45` unique provider request IDs across the primary session and its subagents
- Input tokens: `21,748`
- Cache-creation input tokens: `200,841`
- Cache-read input tokens: `1,299,879`
- Output tokens: `35,051`
- Total tokens including cache traffic: `1,557,519`
- Output characters returned through bridge: `3631`
- Full design-report characters recovered from Claude plan artifact: `29781`
- Bridge topology: `single`
- Bridge total duration: `790798 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/moret-bailly/stage-1-prompt-opus48-primary.md`
- Repository mutation authority: read-only; no model repository edits permitted
- Claude plan source: `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-giggly-octopus.md` (copied verbatim below into the governed component evidence)

## Bridge completion message

I've written the complete Stage-1 design report to the plan file. Let me present it.

★ Insight ─────────────────────────────────────
- **Why `UNCERTAIN` and not `OBSTRUCTION`:** an obstruction forces redesign or halts all progress. Here the interface *is* frozen and there's a genuinely buildable first slice — the blockers are two externalized *gates* (missing primary source text; missing `T(L_v)`-topology primitive), not a design dead-end. Naming them as gates rather than papering over them is the disciplined move the brief demands.
- **The first slice is deliberately gate-independent:** `linearDisjoint_of_compositum` is pure field theory on FOUND Mathlib API, proves real content (it retires the pairwise-vs-joint disjointness edge / counterexample #2), and is needed no matter how G1/G2 resolve. That is what makes it a *true adapter lemma* rather than a restatement of the conclusion.
- **The load-bearing non-leak:** total reality, even degree, and unramified-vs-split are all kept *out* of `moret_bailly_point` — total reality is recovered downstream by prescribing `L_v = ℝ` at infinite places, exactly so risk R4 (silent split↔unramified substitution) can never fire inside the reusable source theorem.
─────────────────────────────────────────────────

The design report is complete in the plan file. Summary of the deliverable:

- **VERDICT: `UNCERTAIN`** — a source-faithful *interface* for `FLT.PotentialModularity.moret_bailly_point` is frozen (matching the blueprint restatement at `chtopbestiary.tex:255`), with exact consumer inventory, clean two-layer architecture, counterexamples, library matches, and a kernel-clean first slice. Two named gates block promotion to `READY-FOR-GPT-REVIEW`:
  - **G1 (source gate, hard):** the primary Moret–Bailly 1989 text is absent locally; SRC-011 records no theorem number/page — exact fidelity to the primary source cannot be certified.
  - **G2 (foundational-primitive gate):** no `rationalPoint` API and no topology on `T(L_v)` in the pinned Mathlib — the prescribed-local-open hypothesis can't fully elaborate without prerequisite definitions.
- **Everything absent in Lean** (both consumers too), so the design is an interface freeze, not a code retrofit.
- **First buildable slice:** `linearDisjoint_of_compositum` in `FLT/PotentialModularity/AuxiliaryField.lean` — provable today, retires the joint-vs-pairwise disjointness edge.
- **Six open routing questions** for the GPT-5.6 reviewer/operator (G1 routing, curve-vs-variety scope, G2 cost, place representation, adapter ownership, first-slice acceptance).

The full report — VERDICT / CURRENT EXACT BOUNDARY / SOURCE AND CONSUMER AUDIT / DEPENDENCY GRAPH / PROPOSED LEAN SIGNATURES / LIBRARY MATCHES / COUNTEREXAMPLES AND FAILURE MODES / FIRST BUILDABLE SLICE / STOP-LOSS GATE / DEFINITION OF READY / OPEN QUESTIONS — is in `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-giggly-octopus.md`.

One point worth your decision before any build proceeds: **the verdict hinges on G1 routing.** If you (as operator) authorize adopting the FLT blueprint's restatement as the *authoritative frozen source contract* (rather than requiring the 1989 primary text), the verdict promotes to `READY-FOR-GPT-REVIEW` on the interface; otherwise it stays `UNCERTAIN` pending the primary source. That is genuinely your call, not the model's, since it defines what "source-faithful" is allowed to mean for this component.

## Full primary design report

# Primary Opus 4.8 Stage-1 Design — FLT-MORET-BAILLY

Produced component: `FLT-MORET-BAILLY` → proposed Lean `FLT.PotentialModularity.moret_bailly_point`.
Role: first-attempt primary producer under the Opus-first ladder. Work read-only, independent
(no prior Stage-1 model output exists or was consulted — `stage-1-attempts.md` records all prior
lanes as `CANCELLED / SUPERSEDED / NO VERDICT`).

- Repo: `/Volumes/second-store/devel/proof-forks/FLT`
- Branch: `methodology/varro-proof-program-20260716`; HEAD `66e4f1e`; work-order start SHA `827eb96`
- Pinned Mathlib rev: `a3364faec42918fcd84a03a255b50570129f9ead`; toolchain `leanprover/lean4:v4.32.0-rc1`
- Build config: `lakefile.toml` (no root `lakefile.lean`)

---

## 1. VERDICT — `UNCERTAIN`

A source-faithful **interface** for `moret_bailly_point` can be, and below is, frozen at the level of
the FLT blueprint's own restatement of Moret–Bailly (`blueprint/src/chapter/chtopbestiary.tex:255`).
The consumer inventory is exact, the two-layer architecture is clean, and there is a genuinely
kernel-clean first slice (a pure field-theory disjointness adapter). But two named gates block a
`READY-FOR-GPT-REVIEW` promotion, and neither is a matter of model effort:

- **G1 — Source-text gate (hard).** The primary source (SRC-011, Moret–Bailly, *Groupes de Picard et
  problèmes de Skolem I, II*, 1989, Ann. Sci. ENS 22, 161–194) is **not present locally**, and
  `SOURCE-REGISTER.md:19` records **no theorem number and no page** — only "Primary source identified;
  exact Lean statement absent." The only locally-verifiable statement is the FLT blueprint's
  restatement, itself a secondary and "explicitly incomplete" source (SRC-004). I therefore cannot
  certify exact-hypothesis fidelity to the 1989 paper (variety generality, exact smoothness/geometric
  hypotheses, the precise form of the local opens and disjointness) without hallucinating. Per the
  brief (lines 39–40) this is recorded as a **source gate**, not a proof.
- **G2 — Foundational-primitive gate (definition gap).** The prescribed-local-behaviour hypothesis
  requires a **topology on `T(L_v)`** (local points of a variety/curve over a local field) and a
  first-class **`L`-point** object. Both are **NONE FOUND** in the pinned Mathlib (`rationalPoint`
  absent; no local-point topology). The blueprint itself says "we do not even have the definition of a
  curve over a field in Lean" (`chtopbestiary.tex:268`). The full source statement cannot fully
  elaborate until these prerequisite definitions are supplied.

Because I converged on a concrete, non-strengthened interface with counterexample checks and a
buildable slice, the verdict is `UNCERTAIN` (design advanced, freeze blocked), **not** `OBSTRUCTION`
(no redesign is forced) and **not** `REVISE` (nothing produced is wrong). Promotion to
`READY-FOR-GPT-REVIEW` requires closing G1 (obtain/quote the primary text, or an operator decision to
adopt the blueprint restatement as the authoritative source contract) and scoping G2 (accept the
prerequisite-definition cost, or restrict the frozen statement to an affine/coordinate model where
`T(L_v)`'s topology comes for free from the local field).

---

## 2. CURRENT EXACT BOUNDARY

- **Lean state: absent.** Grep for `moret`/`bailly`/`moret_bailly_point` over `**/*.lean` returns
  **zero hits**. No `FLT/PotentialModularity/` directory exists. `proof-obligations.ndjson`:
  `FLT-MORET-BAILLY.current_state = "absent"`, `kernel_probe_state = "absent"`,
  `review_state = "unreviewed"`, `direct_dependencies = []`, `graph_depth = 0`, on `critical_path`.
- **Both consumers absent too.** `FLT-AUX-CURVE` (`exists_auxiliary_curve`) `current_state = "absent"`;
  `FLT-AUX-LOCAL-FIELD` (`AuxiliaryFieldCondition`) `current_state = "definition-gap"`,
  `review_state = "revision-required"`. There are **no `sorry`/`axiom`/`admit` stubs to retire** —
  the "stubs" live purely in the planning ndjson layer.
- **Design state: `dor: BLOCKED`.** `source-design.ndjson` component `moret-bailly` (owner FLT-303):
  `primary_source_exact: true` but `hypothesis_translation/proof_outline/sublemma_graph/`
  `counterexample_review/library_matches/lean_signature` all `false`;
  `next_gate: "…extract the exact local-open, disjointness, parity, and rational-point theorem."`
- **Library match: `absent`.** `library-matches.ndjson` MISS-005 verdict `absent` — "No source-faithful
  prescribed-local-behaviour point theorem with required disjointness was located." MISS-014 (AUX-LOCAL-
  FIELD) verdict `blocked` — predicate "cannot be frozen until the lifting theorem selects
  split-completely or unramified local behaviour."
- **Live risk R4** (`RISK-REGISTER.md:8`): "Taylor's split-completely condition is silently weakened to
  unramified … Terminal … choose Taylor or Gee before construction." This governs the consumer, not the
  source theorem, but the frozen interface must keep it that way.

---

## 3. SOURCE AND CONSUMER AUDIT

### 3.1 Frozen source statement (locally verifiable text)

Verbatim, `blueprint/src/chapter/chtopbestiary.tex:255–266` (with the obvious typo `(L_v)` → `T(L_v)`):

> Let `K^avoid/K` be a Galois extension of number fields. Suppose `S` is a finite set of places of `K`.
> For `v∈S` let `L_v/K_v` be a finite Galois extension. Suppose `T/K` is a smooth, geometrically
> connected curve and for each `v∈S` a nonempty, `Gal(L_v/K_v)`-invariant, open subset
> `Ω_v ⊆ T(L_v)`. Then there is a finite Galois extension `L/K` and a point `P ∈ T(L)` such that:
> (i) `L/K` is Galois and linearly disjoint from `K^avoid` over `K`;
> (ii) if `v∈S` and `w|v` in `L` then `L_w/K_v ≅ L_v/K_v`;
> (iii) `P ∈ Ω_v ⊆ T(L_v) ≅ T(L_w)` via one such `K_v`-algebra morphism.

### 3.2 Hypothesis-by-hypothesis translation (each marked verified-locally / UNVERIFIED-vs-primary)

| # | Source clause | Meaning | Status |
|---|---|---|---|
| H1 | `K^avoid/K` Galois ext. of number fields | fixed finite Galois avoidance extension | verified-locally; primary text UNVERIFIED |
| H2 | `S` finite set of **places** (finite + infinite) | index set of local conditions | verified-locally; **note: consumer needs both kinds** |
| H3 | `L_v/K_v` finite **Galois** local ext. | prescribed local extension at each `v` | verified-locally; UNVERIFIED vs primary |
| H4 | `T/K` smooth, geometrically connected **curve** | the moduli variety; blueprint restricts to a curve | verified-locally; **narrower than Moret–Bailly's variety generality — UNVERIFIED** |
| H5 | `Ω_v ⊆ T(L_v)` nonempty, `Gal(L_v/K_v)`-invariant, **open** | prescribed local behaviour | verified-locally; openness is in the `v`-adic topology on `T(L_v)` — see G2 |
| C1 | `L/K` finite Galois, **linearly disjoint** from `K^avoid` | disjointness conclusion | verified-locally |
| C2 | `L_w/K_v ≅ L_v/K_v` for a prime `w|v` | prescribed splitting/ramification behaviour | verified-locally |
| C3 | `P ∈ Ω_v` under `T(L_v)≅T(L_w)` | global point meets every local open | verified-locally |

**No total-reality, even-degree, Galois-closure, quaternion-splitting, good-reduction, or
"unramified/split" clause appears in the source statement.** Those are all consumer-side.

### 3.3 Exact consumer inventory (who reads what)

Proof-graph edges: `E-MORET-BAILLY-AUX-CURVE` and `E-MORET-BAILLY-AUX-LOCAL-FIELD`. Only two direct
consumers; both owned by FLT-413 component `auxiliary-residual-image` (`dor: BLOCKED`).

**Datum → produced-by (source clause) → consumed-by (obligation `lean_type`):**

| Needed datum | Source clause | Consumer that reads it |
|---|---|---|
| extension `L/K` | "finite Galois extension `L/K`" | AUX-CURVE "even-degree totally real Galois extension F"; AUX-LOCAL-FIELD "totally real auxiliary field" |
| point `P ∈ T(L)` | "point `P ∈ T(L)`" | AUX-CURVE: the moduli point = elliptic curve `A/F` with `A[ℓ] ≅ ρ|G_F`, `A[p]` induced |
| disjointness from `K^avoid` | clause (i) | AUX-CURVE "disjoint from the residual kernel"; AUX-LOCAL-FIELD "disjoint from the **two** residual/cyclotomic avoidance extensions" |
| local behaviour at finite `v` | clauses (ii),(iii) | AUX-LOCAL-FIELD "both selected primes **unramified**, curve has **good reduction** above them"; AUX-CURVE "all local conditions required by MLT" |
| archimedean behaviour | clauses (ii),(iii) at infinite `v` | **total reality of `F`** — realized by prescribing `L_v = ℝ` at real places (a *consequence* of instantiation, not a source hypothesis) |
| even degree / Galois closure / quaternion splitting | **NOT in source** | AUX-CURVE/AUX-LOCAL-FIELD flag these explicitly as "project/Jacquet–Langlands requirements, not source hypotheses" |

### 3.4 The corrected Taylor-2018 distinction (must be preserved, must not leak in)

`review/gpt56xhigh-source-correction.md:8–18` + `CONVERGENCE.md:24` + `modularity-lifting-source-audit.md`
+ R4: **Taylor 2018 Thm 2.1.1 requires the witness to be *unramified* at `v|ℓ` — an at-`ℓ`
condition — NOT complete splitting** (Taylor 2006 Thm 3.3 is stronger; it demands complete splitting).
`AUX-LOCAL-FIELD.source_condition_risks`: "Taylor 2018 requires unramifiedness, not complete
splitting." **Design consequence:** `moret_bailly_point` must *not* fix the local shape to either
"unramified" or "split." It prescribes the **full local Galois extension `L_v`** (clause ii); the
consumer selects `L_v/K_v` unramified (for good reduction / unramified-at-ℓ) when instantiating.
Baking "unramified" or "split" into the source theorem is the precise accidental-strengthening R4 warns
of. MISS-014 confirms the AUX-LOCAL-FIELD predicate "cannot be frozen until the lifting theorem selects
split-completely or unramified" — i.e. that selection is the consumer's, downstream of `FLT-MLT-SOURCE`.

---

## 4. DEPENDENCY GRAPH (transitively reduced)

Nodes P0–P4 are prerequisite definitions this design must introduce (all NONE FOUND / partial in
Mathlib); MB is the frozen source theorem; A1/A2 are project adapters; consumers on the right.

```
        Mathlib FOUND primitives
        (NumberField, IsGalois, IsTotallyReal,
         InfinitePlace, HeightOneSpectrum, adicCompletion,
         InfinitePlace.Completion, Valued, Smooth, GeometricallyIntegral/Connected,
         Scheme.Opens, IsUnramified, IntermediateField.LinearDisjoint, Algebra.IsPushout)
                 │
     ┌───────────┼───────────────────────────┐
     ▼           ▼                           ▼
 P0 Scheme.pointsOver        P1 localPointTopology     P2 KAvoid bundle (Galois/finite)
 (L-points as Spec L⟶T)      (v-adic topology on T(L_v))       │
     │           │  ⚠G2               │                       │
     └─────┬─────┘                    │                       │
           ▼                          ▼                       │
       P3 LocalCondition  (nonempty, Gal-invariant open Ω_v ⊆ T(L_v))
           │                                                  │
           └──────────────────────┬───────────────────────────┘
                                   ▼
                     ┌─────────  MB: moret_bailly_point  ─────────┐   ⚠G1 (source gate)
                     │  in: K, K^avoid, S(finite∪infinite), {L_v}, T, {Ω_v}
                     │  out: L (finite Galois), P∈T(L),
                     │       LinearDisjoint L K^avoid, L_w≅L_v, P∈Ω_v
                     └──────────────┬───────────────────────┬────┘
                                    ▼                       ▼
              A1 disjointness_of_compositum          A2 AuxiliaryFieldCondition bridge
              (joint→pairwise, pure field thy)       (source opens ⇒ unram + good red + 2×disjoint;
                     │                                project even-deg/Galois/quat exposed separately)
                     └──────────────┬───────────────────────┘
                                    ▼
              FLT-AUX-LOCAL-FIELD  ─────────►  FLT-AUX-CURVE  ─────►  FLT-POTMOD
              (E-MORET-BAILLY-AUX-LOCAL-FIELD)  (E-MORET-BAILLY-AUX-CURVE; also E-CLASS-FIELD/…)
```

**Build gates:** G1 gates MB's *promotion to source-certified* (not its interface). G2 (P0,P1,P3)
gates MB's *full elaboration*. A2's local-shape (unramified vs split) is gated downstream by
`FLT-MLT-SOURCE` (BLOCKED) — do not freeze it here.

---

## 5. PROPOSED LEAN SIGNATURES (dependency order)

Two layers, per the brief: **(a)** source-faithful theorem with only source hypotheses/conclusions;
**(b)** project adapters carrying all FLT-specific mathematics. Nothing project-specific leaks into (a).
`⚠` marks a term depending on a NONE-FOUND primitive (G2).

### Layer 0 — prerequisite definitions (NONE FOUND — must be supplied)

```lean
-- P0. L-points of a K-scheme.  ⚠ NONE FOUND: no `Scheme.rationalPoint`.
-- An L-point of T over the base Spec K is a K-morphism Spec L → T.
abbrev Scheme.pointsOver {K : CommRingCat} {T : Scheme} (p : T ⟶ Spec K)
    (L : CommRingCat) (sL : Spec L ⟶ Spec K) : Type _ :=
  { P : Spec L ⟶ T // P ≫ p = sL }

-- P1. v-adic topology on local points.  ⚠ NONE FOUND: no topology on T(L_v).
-- For a local field L_v (Valued / IsNonarchimedeanLocalField, or ℝ/ℂ), the set of
-- L_v-points of T carries a natural topology; Mathlib has it for the *field*, not for T(·).
-- Frozen as a typeclass to be discharged by a coordinate model on an affine chart of T.
class LocalPointTopology {K : CommRingCat} {T : Scheme} (p : T ⟶ Spec K)
    (Lv : CommRingCat) [/- Lv a local field -/] (sLv : Spec Lv ⟶ Spec K) : Type _ where
  topology : TopologicalSpace (Scheme.pointsOver p Lv sLv)

-- P2. A finite Galois avoidance extension, bundled.
structure GaloisAvoid (K : Type*) [Field K] [NumberField K] where
  {carrier : Type*} [field : Field carrier] [alg : Algebra K carrier]
  [fin : FiniteDimensional K carrier] [gal : IsGalois K carrier]

-- P3. A prescribed local condition at one place (finite or infinite), source-faithful.
-- `Ω` nonempty, Gal(L_v/K_v)-invariant, open in the P1 topology.
structure LocalCondition {K : CommRingCat} {T : Scheme} (p : T ⟶ Spec K)
    (Kv Lv : CommRingCat) (galLvKv : /- L_v/K_v finite Galois -/ Prop)
    (sLv : Spec Lv ⟶ Spec K) [LocalPointTopology p Lv sLv] where
  omega      : Set (Scheme.pointsOver p Lv sLv)
  isOpen     : IsOpen omega            -- ⚠ uses P1
  nonempty   : omega.Nonempty
  galInvariant : True /- Gal(L_v/K_v)-stability of omega; spelled once P0/P1 fixed -/
```

### Layer 1 — source-faithful Moret–Bailly theorem (NO project conclusions)

```lean
/-- `FLT.PotentialModularity.moret_bailly_point` — source-faithful restatement of
    Moret–Bailly (SRC-011) as frozen from `chtopbestiary.tex:255`.  ⚠G1: fidelity to the
    1989 primary text is UNVERIFIED (source absent); this matches the FLT blueprint restatement. -/
theorem moret_bailly_point
    (K : Type*) [Field K] [NumberField K]
    (Kav : GaloisAvoid K)                                   -- H1
    -- H2: finitely many places, split into finite and infinite families (source `S`)
    (Sf : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (Si : Finset (NumberField.InfinitePlace K))
    -- H4: T a smooth, geometrically connected curve over K (relative dim 1)
    {T : Scheme} (p : T ⟶ Spec (CommRingCat.of K))
    (hSm : AlgebraicGeometry.SmoothOfRelativeDimension 1 p)
    (hGC : AlgebraicGeometry.GeometricallyConnected p)
    -- H3 + H5: prescribed finite Galois local extensions and nonempty invariant open conditions
    (locf : ∀ v ∈ Sf, Σ (Lv : CommRingCat), LocalCondition p _ Lv _ _)
    (loci : ∀ v ∈ Si, Σ (Lv : CommRingCat), LocalCondition p _ Lv _ _) :
    -- Conclusion: a finite Galois L/K with a global point meeting every local condition.
    ∃ (L : Type*) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
      (P : Scheme.pointsOver p (CommRingCat.of L) sL),
        -- (C1) linear disjointness from K^avoid
        (IntermediateField.LinearDisjoint /- L over K -/ /- Kav over K -/) ∧
        -- (C2) prescribed local isomorphism L_w/K_v ≅ L_v/K_v at some w|v, all v ∈ Sf ∪ Si
        (∀ v ∈ Sf, ∃ w, /- L_w/K_v ≅ L_v/K_v -/ True) ∧
        (∀ v ∈ Si, ∃ w, /- L_w/K_v ≅ L_v/K_v -/ True) ∧
        -- (C3) the global point lands in every local open Ω_v
        (∀ v ∈ Sf, /- image of P in T(L_v) ∈ Ω_v -/ True) ∧
        (∀ v ∈ Si, /- image of P in T(L_v) ∈ Ω_v -/ True)
```

Notes on binding: `K^avoid`, extension `L`, scheme/curve `T`, finite+infinite place sets, local fields
`L_v`, opens `Ω_v`, the `L`-point `P`, and the disjointness are all bound. The `True`/`_`-marked
sub-terms are exactly the G2-blocked pieces (local-point map, `T(L_v)` topology, local-iso spelling):
they are *identified*, not hidden, and become concrete once P0/P1/P3 are discharged.

### Layer 2 — project adapters (all FLT-specific mathematics lives here)

```lean
-- A1. Joint→pairwise disjointness. Pure field theory, FOUND primitives only. (First slice — §8.)
theorem linearDisjoint_of_compositum
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L K1 K2 : IntermediateField K Ω)
    (h : L.LinearDisjoint (K1 ⊔ K2)) : L.LinearDisjoint K1 ∧ L.LinearDisjoint K2

-- A2. Auxiliary-field bridge: the source opens/disjointness SUPPLY the project conditions,
--     which are exposed as SEPARATE fields (even degree / Galois / quaternionic NOT source hyps).
--     ⚠ Local shape (unramified vs split) is chosen HERE, gated by FLT-MLT-SOURCE — do not freeze now.
structure AuxiliaryFieldCondition
    (F : Type*) [Field F] [NumberField F] (ell p : ℕ) … : Prop where
  unramified_ell : …          -- from a Sf-local condition with L_v/K_v unramified at v|ell
  good_reduction : …          -- from a Sf-local condition at v|p
  disjoint_res   : …          -- from C1 with K^avoid = (residual kernel ⊔ cyclotomic) compositum
  disjoint_cyc   : …          -- (A1 splits the joint disjointness back to the two factors)
  -- project-only, exposed separately, NOT derived from the source theorem:
  totallyReal    : NumberField.IsTotallyReal F     -- from prescribing L_v = ℝ at Si real places
  evenDegree     : Even (Module.finrank ℚ F)       -- project/Jacquet–Langlands requirement
  isGalois       : IsGalois ℚ F
```

---

## 6. LIBRARY MATCHES (pinned rev `a3364fa…`)

| Proposed node | Pinned declaration | Verdict |
|---|---|---|
| number field `K` | `NumberField` — `Mathlib/NumberTheory/NumberField/Basic.lean:43` | FOUND |
| `IsGalois K L` | `IsGalois` — `Mathlib/FieldTheory/Galois/Basic.lean:58` | FOUND |
| total reality (adapter) | `NumberField.IsTotallyReal` — `…/InfinitePlace/TotallyRealComplex.lean:47` | FOUND |
| infinite places / real | `NumberField.InfinitePlace(.IsReal)` — `…/InfinitePlace/Basic.lean:57,179` | FOUND |
| finite places | `IsDedekindDomain.HeightOneSpectrum` — `…/DedekindDomain/Ideal/Lemmas.lean:495` | FOUND |
| finite adeles / completions | `FiniteAdeleRing`, `HeightOneSpectrum.adicCompletion` — `…/DedekindDomain/*` | FOUND |
| infinite-place completion | `NumberField.InfinitePlace.Completion` — `…/Completion/InfinitePlace.lean:81` | FOUND |
| **linear disjointness** | `IntermediateField.LinearDisjoint` — `Mathlib/FieldTheory/LinearDisjoint.lean:157` (also `Subalgebra`/`Submodule`, `RingTheory/DedekindDomain/LinearDisjoint.lean`) | FOUND |
| base change / pushout | `Algebra.IsPushout` (+`equiv`) — `Mathlib/RingTheory/IsTensorProduct.lean:620` | FOUND |
| scheme / `Spec` / `Hom` | `AlgebraicGeometry.Scheme`,`Scheme.Spec`,`Scheme.Hom` — `…/Scheme.lean:42,482,74` | FOUND |
| geometric integrality/connectedness | `GeometricallyIntegral`/`GeometricallyConnected` (**morphism**, relative) — `…/Geometrically/Integral.lean:40`, `…/Geometrically/Connected.lean` | FOUND (relative to base — correct shape) |
| smooth (rel. dim 1) curve | `Smooth`, `SmoothOfRelativeDimension` — `…/Morphisms/Smooth.lean:62,135` (spelling is `Smooth`, not `IsSmooth`) | FOUND (no bundled `Curve` type) |
| Zariski open subscheme | `Scheme.Opens := TopologicalSpace.Opens X` — `…/Scheme.lean:71` | FOUND — **distinct from** topological `IsOpen` on `T(L_v)` |
| unramified (∞ / finite) | `InfinitePlace.IsUnramified` — `…/InfinitePlace/Ramification.lean:184`; completion-side `…/Completion/Ramification.lean`; `Algebra.FormallyUnramified` | FOUND |
| nonarch. local field | `IsNonarchimedeanLocalField` — `…/LocalField/Basic.lean:45` | FOUND (no umbrella `IsLocalField`) |
| **`T(L)` / rational point** | — | **NONE FOUND** (no `rationalPoint`; build as `Spec L ⟶ T`) |
| **topology on `T(L_v)`** | — | **NONE FOUND** (P1) — the core G2 gap |
| **points over completion vs global field** | — | **NONE FOUND as predicate** — encode manually via coefficient object (`adicCompletion`/`Completion` vs `K`) |
| **prescribed-local-behaviour point theorem** | — | **NONE FOUND** (MISS-005 `absent`) |

`LIBRARY-SURVEY.md`: "Moret-Bailly with the required disjointness" is listed among "consequential
missing interfaces." `FLT/Assumptions/README.md:39`: Moret–Bailly classed as statable-but-unformalized.

---

## 7. COUNTEREXAMPLES AND FAILURE MODES (hostile checks)

1. **Independent local witnesses that don't globalise.** Nonempty `Ω_v` at each `v` does *not* by
   itself give a global `P` — that is the entire content of Moret–Bailly. Do **not** model the theorem
   as `(∀ v, Nonempty Ω_v) → Nonempty(global)` via a product/independence assumption. The brief forbids
   "assume independence of field conditions." The theorem's power is the *simultaneous* global point.
2. **Pairwise vs joint disjointness.** The consumer needs disjointness from **two** avoidance
   extensions `K1` (residual kernel), `K2` (cyclotomic). The source gives disjointness from a single
   `K^avoid`. Correct adapter: set `K^avoid = K1 ⊔ K2` (Galois since both are) and derive both via A1.
   **Failure:** running the theorem twice with `K1`, `K2` separately yields two *different* fields `L`,
   `L'` — useless. Must use the compositum, once.
3. **Splitting silently substituted for unramifiedness (R4, terminal).** Fixing `L_v/K_v` trivial
   (`L_v = K_v`, complete splitting) in the *source theorem* over-constrains and mis-serves Taylor
   2018 (needs unramified, not split). Keep `L_v` a free prescribed extension; let A2 pick unramified.
4. **Galois closure destroying local conditions.** The output `L/K` is already Galois; but if an adapter
   later takes a further Galois/normal closure of `L` over `ℚ` (to get "Galois over ℚ"), that closure
   can change `L_w/K_v` and break clause (ii). The even-degree/Galois-over-ℚ must be arranged by
   *choice of `T`, `S`, `Ω_v`, `K^avoid`* upstream, not by post-hoc closure. Guard in A2.
5. **Total reality / even degree asserted without construction.** Neither is a source conclusion.
   Total reality must be *realized* by an infinite-place local condition `L_v = ℝ`; even degree is a
   project requirement. A design that puts `IsTotallyReal L` or `Even (finrank)` into
   `moret_bailly_point`'s conclusion is accidental strengthening — rejected.
6. **Empty local opens.** `Ω_v = ∅` makes the hypothesis vacuously unsatisfiable but the *theorem*
   false-if-stated-without `nonempty`. `LocalCondition.nonempty` is mandatory; dropping it yields an
   unprovable statement (no `P` can meet an empty open).
7. **Rational points over the wrong field.** `P ∈ T(L)` (global extension) vs `P ∈ T(L_v)`
   (completion) vs `P ∈ T(K)` are distinct. The output point is over the *global* `L`; membership in
   `Ω_v` is checked after mapping `T(L) → T(L_v)` at `w|v`. Conflating `T(L_v)` with `T(L)` (or Zariski
   `Scheme.Opens` with the `v`-adic-topological `Ω_v`) is the P1/coefficient-object trap — flagged in
   §6 as two separate NONE-FOUND items.
8. **Circular use of the auxiliary-curve theorem.** `moret_bailly_point` must **not** reference
   `exists_auxiliary_curve` or any elliptic-curve/moduli fact — it has `direct_dependencies = []`.
   The moduli-variety `T` is an *input*; constructing `T` (the auxiliary moduli problem) is AUX-CURVE's
   job. Any dependency edge MB→AUX-CURVE reversed is a cycle — reject.
9. **Curve-vs-variety scope drift.** The blueprint freezes a *curve*; Moret–Bailly's paper is about
   varieties. Stating the Lean theorem for a general variety without the primary text is unverified
   strengthening of scope; stating it for a curve is faithful to what is locally checkable. Freeze the
   curve; log the generalization as source-gated.

---

## 8. FIRST BUILDABLE SLICE (kernel-clean, retires a real edge)

**Slice = adapter lemma A1 `linearDisjoint_of_compositum`** — a *true adapter lemma*, not a restatement
of the desired conclusion, provable today from FOUND primitives with no `sorry`.

- **File/module:** `FLT/PotentialModularity/AuxiliaryField.lean` (new; matches
  `expected_module = FLT.PotentialModularity.AuxiliaryField`).
- **Imports:** `Mathlib.FieldTheory.LinearDisjoint` (+ `Mathlib.FieldTheory.Galois.Basic`).
- **Statement:** as in A1 (§5): `L.LinearDisjoint (K1 ⊔ K2) → L.LinearDisjoint K1 ∧ L.LinearDisjoint K2`.
- **Proof shape:** monotonicity of linear disjointness under `K1 ≤ K1 ⊔ K2` (a `K`-basis of `L` that is
  linearly independent over `K1 ⊔ K2` is a fortiori independent over the subfield `K1`); use the
  `IntermediateField.LinearDisjoint` API's restriction/`mono` lemmas. Pure, terminating, kernel-clean.
- **Graph edge retired:** the **pairwise-vs-joint disjointness** edge feeding `AUX-LOCAL-FIELD`
  (`disjoint_res`/`disjoint_cyc` in A2) — closes counterexample #2 mechanically and is a prerequisite
  the AUX-LOCAL-FIELD predicate needs regardless of how G1/G2 resolve.
- **Why not the MB structure first:** the `MoretBaillyPoint`/`LocalCondition` bundles (P0–P3) are also
  elaboratable as *data*, but they depend on the G2 primitives and edge close to a restatement of the
  conclusion; A1 is the maximal genuine-proof-content unit that is independent of both gates.

**Explicitly not in the first slice:** the MB theorem body (G1+G2), the P1 topology, and A2's local
shape (gated by `FLT-MLT-SOURCE`).

---

## 9. STOP-LOSS GATE

Halt and escalate to operator authorisation at the **first** of these — all currently tripped or
imminent:

- **G1 tripped (missing source fact).** Primary Moret–Bailly text absent; no theorem number/page in
  SRC-011. Do not certify `moret_bailly_point` as source-faithful beyond "matches the blueprint
  restatement." Escalation options: (a) operator supplies/authorises the 1989 text; (b) operator
  adopts the blueprint restatement as the authoritative frozen source contract (recorded as such);
  (c) accept T2 "named sourced historical boundary" per the obligation's `proof_pattern` if pre-1990
  scope is accepted.
- **G2 tripped (absent foundational API).** No `rationalPoint`, no `T(L_v)` topology. Full elaboration
  requires prerequisite definitions P0/P1/P3. Escalation: authorise the prerequisite-definition cost
  (nontrivial), or authorise restricting the frozen statement to an affine/coordinate model where the
  `v`-adic topology on `T(L_v)` is induced from the local field on coordinates.
- **Downstream gate (do not cross here).** A2's unramified-vs-split selection depends on
  `FLT-MLT-SOURCE` (BLOCKED). Freezing `AuxiliaryFieldCondition`'s local shape now would trip R4;
  leave it to the AUX-LOCAL-FIELD owner (FLT-413) after MLT-SOURCE resolves (MISS-014).
- **Incompatible-signature gate.** If, on discharging P1, the natural `T(L_v)` topology cannot be made
  `Gal(L_v/K_v)`-equivariant in the pinned library, the `LocalCondition.galInvariant` field is
  unstatable → redesign required (report back before proceeding).

---

## 10. DEFINITION OF READY (checklist)

| DoR item | State | Evidence |
|---|---|---|
| Source exactness | **PARTIAL / GATED** | blueprint text frozen (`chtopbestiary.tex:255`); primary SRC-011 absent (G1) |
| Hypothesis translation | **DONE** (vs blueprint) / **GATED** (vs primary) | §3.2 table, each clause marked |
| Proof outline | **NOT DONE** | `source-design.ndjson`: `proof_outline: false`; only a strategy sketch exists |
| Sublemma graph | **DONE (design-level)** | §4 (P0–P4, MB, A1, A2, consumers), transitively reduced |
| Counterexample review | **DONE** | §7 (9 hostile cases incl. all brief-listed ones) |
| Library matches | **DONE** | §6, exact pinned decls or NONE FOUND |
| Elaborated signatures | **PARTIAL / GATED** | §5; MB body G2-blocked terms identified; A1 fully elaboratable |
| DoR verdict | **BLOCKED** (matches `source-design.ndjson` `dor: BLOCKED`) | promote on G1 close + G2 scoping |

---

## 11. OPEN QUESTIONS FOR SYNTHESIS (for GPT-5.6 reviewer / operator)

1. **G1 routing:** obtain the Moret–Bailly 1989 primary text, or authorise adopting the blueprint
   restatement as the frozen source contract? (Determines whether `UNCERTAIN` → `READY-FOR-GPT-REVIEW`.)
2. **Scope:** freeze the **curve** form (blueprint-faithful, locally verifiable) or the general
   **variety** form (true Moret–Bailly generality, but source-gated)? Recommendation: curve.
3. **G2 scoping:** pay for the `T(L_v)`-topology + `L`-point prerequisite definitions (P0/P1/P3), or
   restrict the frozen statement to an affine/coordinate model? Which is cheaper for the pinned rev?
4. **Place representation:** two families (`HeightOneSpectrum` finite + `InfinitePlace`) as in §5, or a
   unified place type? Total reality *needs* the infinite family (prescribe `L_v = ℝ`) — confirm this is
   accepted as the mechanism (a consequence, not a source hypothesis).
5. **Adapter ownership:** confirm A2 (`AuxiliaryFieldCondition` local shape) stays with FLT-413 and is
   not frozen until `FLT-MLT-SOURCE` selects unramified-vs-split (MISS-014 / R4).
6. **First slice acceptance:** is A1 `linearDisjoint_of_compositum` accepted as the first kernel-clean
   unit, landing in `FLT/PotentialModularity/AuxiliaryField.lean`?
```
