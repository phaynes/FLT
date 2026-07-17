# Stage 1 primary design — Opus 4.8

## Model and transport evidence

- Agent: `opus48-primary-designer-d10`
- Configured model: `claude-opus-4-8`
- Backend transport: `claude-code`
- Role: `primary`
- Difficulty: `10/10`
- Scheduled design budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `774945 ms`
- Claude session: `bc4a68a4-8bdb-4c7f-a628-11cc6ede9f3a`
- Token audit: `51` unique provider request IDs across the primary session and its subagents
- Input tokens: `41,712`
- Cache-creation input tokens: `213,759`
- Cache-read input tokens: `2,018,349`
- Output tokens: `47,709`
- Total tokens including cache traffic: `2,321,529`
- Output characters returned through bridge: `1887`
- Full design-report characters recovered from Claude plan artifact: `29294`
- Bridge topology: `single`
- Bridge total duration: `774945 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/fontaine-odlyzko/stage-1-prompt-opus48-primary.md`
- Repository mutation authority: read-only; no model repository edits permitted
- Claude plan source: `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-tranquil-willow.md` (copied verbatim below into the governed component evidence)

## Bridge completion message

The `ExitPlanMode` tool is not available in this session, so I cannot formally exit plan mode via the tool. The planning deliverable is nonetheless complete and finalized.

**Design delivered** — `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-tranquil-willow.md` contains the full source-faithful Stage-1 report for `FLT-FONTAINE-ODLYZKO`:

- **Verdict `UNCERTAIN`** with the two blocking soundness-boundary reasons stated up front.
- All 11 required sections plus verification: exact current boundary, source/consumer audit with per-implication locators (resolved vs unresolved), the C0–C4 mathematical case graph, elaboration-ready Lean signatures in dependency order, library matches against the pinned Mathlib (`a3364fae…`) with exact locators or `NONE FOUND`, eight hostile counterexample checks, the buildable **Slice A**, the **G1–G4 stop-loss gate**, the DoR checklist (component remains BLOCKED), and open questions for GPT-5.6 xhigh review.

**Key produced findings (not citations):**
- `[Algebra ℤ_[3] k]` + `[Finite k]` *forces* `CharP k 3`; coverage must span all `𝔽_{3^r}` — this is the safe, axiom-free first slice.
- `Odlyzko_statement` (deg ≥ 18, base 8.25) is provably insufficient; the route needs additional named pre-1990 axioms (Fontaine/Serre flat-disc upper bound, small-degree minima for `A₄`/dihedral, Dickson `PGL₂` classification), none present in the tree.
- The `mod_three` conclusion is orientation-critical (trivial **quotient**, cyclotomic **sub**); the opposite-orientation hardly-ramified extension is a candidate counterexample whose exclusion (peu-ramifiée Selmer vanishing) gates statement correctness.

No repository source files were edited and no proof was attempted; the stop-loss gate prohibits building past Slice A without operator sign-off on the expanded axiom boundary and the C2(ii) orientation question.

## Full primary design report

# PRIMARY OPUS 4.8 DESIGN — FLT-FONTAINE-ODLYZKO (Stage 1, read-only)

Component `fontaine-odlyzko` · obligation `FLT-FONTAINE-ODLYZKO` · owner `FLT-307` ·
target stage **T2** · difficulty 10/10 · pinned Mathlib
`a3364faec42918fcd84a03a255b50570129f9ead` · start SHA `827eb96`.

Producer role: first-attempt primary under the Opus-first ladder. No edits made outside this
plan file; no proof attempted. A citation, scaffold, `sorry`, or axiom is never treated as proof.

---

## 0. TERMINAL VERDICT — `UNCERTAIN`

The Fontaine/Serre/Poitou–Odlyzko route to `modThree_classification_core` is mathematically
sound and source-exact, and I give below its exact case graph, elaboration-ready Lean signatures,
a transitively-reduced dependency graph, a join theorem, library matches, hostile counterexamples,
and a first buildable kernel-clean slice. I return **`UNCERTAIN`** rather than `READY-FOR-GPT-REVIEW`
for two soundness-boundary reasons that I must not decide unilaterally and that a reviewer/operator
must adjudicate before build:

1. **The T2 axiom boundary as currently instantiated is provably insufficient.** The only
   historical numerical input present is `Odlyzko_statement` (`FLT/Assumptions/Odlyzko.lean:58`),
   which bounds `|discr K| ≥ 8.25 ^ n` **only for totally-complex `K` of degree `n ≥ 18`**. The
   classification additionally requires (a) a **root-discriminant UPPER bound** from the flat-at-3 /
   tame-at-2 conditions (Fontaine/Serre), (b) **small-degree (n<18) totally-complex discriminant
   minima** for the residual exceptional image `A₄` (degree 12) and small dihedral fields, and
   (c) a **finite-subgroup classification of `PGL₂`** (Dickson). None of (a),(b),(c) exist in the
   pinned tree. So T2 cannot rest on `Odlyzko_statement` alone; it needs 3–4 *additional* named
   pre-1990 axioms. Whether that expanded boundary is authorized at T2 — versus judged to "hide the
   classification behind a renamed assumption" — is an operator decision.
2. **The reducible-case orientation depends on an unresolved Selmer/peu-ramifiée fact**, not on
   Odlyzko. The theorem demands a *trivial quotient* (0→χ₃→V→𝟙→0). A hardly-ramified extension with
   the *opposite* orientation (0→𝟙→V→χ₃→0, trivial sub, no trivial quotient) is a candidate
   counterexample; excluding it requires vanishing of a hardly-ramified `H¹(G_ℚ, χ₃)`
   (flat-at-3 ⇒ peu ramifiée). This is a genuine lemma, not a citation, and its truth gates the
   *statement's* correctness. It is tractable but unproven here.

Everything needed for an independent synthesis + kernel probe of the **interface skeleton and first
slice** is specified below; the two items above are exactly what GPT-5.6 xhigh review and the
operator must resolve.

---

## 1. CURRENT EXACT BOUNDARY

**Proposed core (absent).** Control decl `FLT.HardlyRamified.modThree_classification_core`
(`proof-obligations.ndjson:26`), expected module
`FLT.GaloisRepresentation.HardlyRamified.ModThreeCore`, `current_state:"absent"`,
`kernel_probe_state:"absent"`, `target_stage:"T2"`, `direct_dependencies:["FLT-HR-DEF"]`,
`source_refs:["SRC-003","SRC-007"]`, `library_candidates:["Odlyzko_statement","FiniteFlatGroupScheme",
"PGL2 finite subgroup classification"]`, completion_gate = *"Core theorem has target-stage-appropriate
axiom closure and covers all finite coefficient fields."* No Lean declaration of this name exists in
any `.lean` file (verified repo-wide); it lives only in methodology metadata + the spec instances.

**Sole consumer (admitted).** `GaloisRepresentation.IsHardlyRamified.mod_three`,
`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27–34`, body is `sorry` (line 34). Exact
signature (verbatim):

```lean
theorem mod_three {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  sorry     -- Γ ℚ := Field.absoluteGaloisGroup ℚ
```

Graph edges (`proof-graph.ndjson:107,108`): `FLT-HR-DEF —definition→ FLT-FONTAINE-ODLYZKO
—theorem→ FLT-MOD3`. `FLT-MOD3` is a leaf (only `#check`ed at
`FLTMethodology/Probes/ExistingContracts.lean:25`; no Lean term invokes it yet).

**What must be produced kernel-cleanly vs. what may remain historical.**
- *Produced kernel-cleanly (T2):* the reduction glue — coefficient-field/char-3 derivation,
  reducible⇒trivial-quotient orientation, irreducible⇒cut-out-field⇒contradiction plumbing, and the
  join `modThree_classification_core → mod_three`.
- *Legitimately historical named inputs (T2 axioms, each pre-1990, none of which is the mod-3
  classification itself):* `Odlyzko_statement` (Poitou/Odlyzko 1977, SRC-007); a Fontaine/Serre
  finite-flat root-discriminant estimate; small-degree totally-complex discriminant minima; and
  Dickson's classification of finite subgroups of `PGL₂` over a finite field. The stop-loss gate
  (§9) forbids collapsing any of these into `knownin1980s` (the catch-all
  `axiom knownin1980s {P:Prop} : P`, `FLT/Assumptions/KnownIn1980s.lean:79`) or into the core
  theorem's own name.

---

## 2. SOURCE AND CONSUMER AUDIT

### 2.1 Consumer decomposition (`mod_three`)
- **Coefficient object `k`:** `[Finite k] [Field k] [Algebra ℤ_[3] k] [DiscreteTopology k]`. There is
  **no `[CharP k 3]`**. Characteristic 3 must be *derived*: for a finite field `k` the algebra map
  `ℤ_[3] → k` cannot be injective (`ℤ_[3]` is infinite), its kernel is the unique nonzero prime
  `(3) ⊂ ℤ_[3]`, hence `𝔽₃ ↪ k` and `CharP k 3`. `k` ranges over **all** `𝔽_{3^r} = GaloisField 3 r`,
  not just `ZMod 3` — this is the "coefficient-field coverage" the completion gate names. LOCATOR:
  standard (`ℤ_[3]` local, residue field `𝔽₃`); Lean helpers `charP_of_injective_algebraMap`
  (`Mathlib/Algebra/CharP/Algebra.lean:24`), `charP_of_card_eq_prime_pow`
  (`Mathlib/Algebra/CharP/CharAndCard.lean:86`).
- **`hV : Module.rank k V = 2`**, `V` finite free — 2-dimensional representation.
- **`hρ : IsHardlyRamified (Odd 3) hV ρ`** unpacks (Defs.lean:96–119) to four fields:
  `det` (det ρ = mod-3 cyclotomic character `χ₃`, via `cyclotomicCharacter`), `isUnramified`
  (unramified outside {2,3}), `isFlat` (`GaloisRep.IsFlatAt` at 3, defined by flat prolongation of
  every `V/I`, `GaloisRep.lean:391`), `isTameAtTwo` (∃ surjection `π:V→R` with quotient char `δ` on
  `G_{ℚ₂}` that is unramified and `δ²=1`).
- **Conclusion (orientation-critical):** a *surjective* `π : V →ₗ[k] k` with `π(ρ g v)=π v` for
  **all** `g∈G_ℚ` — i.e. an invariant **quotient** carrying the **trivial** character. Combined with
  `det ρ = χ₃`, `ker π` is the 1-dim sub with character `χ₃`: `0 → χ₃ → V → 𝟙 → 0`. Trivial is on
  TOP, cyclotomic is the SUB (matches docstring "extension of trivial by cyclo").

### 2.2 Source locators for each nontrivial implication (labelled resolved/unresolved)
| Implication | Primary source | Status |
|---|---|---|
| Mod-3 hardly-ramified ⇒ reducible with trivial quotient | Serre, *Duke* 1987 §4.1 (SRC-005); FLT blueprint ch03freyreduction.tex (SRC-003) | RESOLVED as citation; **no Lean/proof present** |
| Finite subgroups of `PGL₂(𝔽_q)` are cyclic/dihedral/A₄/S₄/A₅/Borel | Dickson (1901) | RESOLVED citation; **NONE FOUND in Mathlib/FLT** |
| Flat-at-3 ⇒ local reps ↔ finite-flat group schemes over `ℤ₃`; peu-ramifiée orientation | Fontaine (1985); Serre 1987 §2 (peu/très ramifiée) | RESOLVED citation; **no finite-flat API exists (planned `FLT.GroupScheme.FiniteFlat`, sorry)** |
| Cut-out field ramified only at {2,3}, tame at 2, bounded at 3 ⇒ root-disc UPPER bound `< 8.25` | Serre/Fontaine conductor-discriminant estimate | **UNRESOLVED**: no explicit locator pinned; not in repo |
| Totally-complex, deg ≥ 18 ⇒ `|discr| ≥ 8.25^n` | Poitou 1977 Exp.6 p.17 (SRC-007) = `Odlyzko_statement` | RESOLVED as **axiom** `FLT/Assumptions/Odlyzko.lean:58` |
| Small-degree (n=12 `A₄`; small dihedral) totally-complex disc minima | Odlyzko / Diaz y Diaz tables (pre-1990) | **UNRESOLVED**: no axiom/table present |
| Complex conjugation odd (`det ρ(c)=χ₃(c)=−1`) ⇒ cut-out field totally complex | standard | RESOLVED citation; Lean bridge absent |

---

## 3. COMPLETE MATHEMATICAL CASE GRAPH

Hypotheses: irreducible-or-not 2-dim `ρ: G_ℚ→GL(V)`, `V` over finite `k`, `char k = 3`,
`det ρ = χ₃` (mod-3 cyclotomic, order 2, ramified only at 3, `χ₃(c)=−1`), unramified outside {2,3},
flat at 3, tame at 2. Target: invariant trivial **quotient**.

- **C0 Coefficient reduction.** Derive `CharP k 3`; `k=𝔽_{3^r}`. The conclusion is invariant under
  extension of scalars `k ↪ k̄` for *existence* of a quotient line **only if** descended back to `k`;
  so the classification is proved over `k̄=𝔽̄₃` for image analysis, then the invariant line is
  shown `Gal(k̄/k)`-stable (Frobenius-semilinear descent) to land in `V ⊗ k`. *Needs separate
  treatment* — this is the "non-prime finite coefficient field" obligation.
- **C1 Reducible vs irreducible dichotomy** on `ρ.toRepresentation` (`GaloisRep.IsIrreducible`,
  `GaloisRep.lean:404`).
- **C2 (reducible).** JH characters `α,β: G_ℚ→k^×`, `αβ=χ₃`, each unramified outside {2,3}.
  The quotient (top) character `γ` satisfies: unramified outside {2,3}; `γ|_{G₂}` unramified with
  `γ²=1` (from `isTameAtTwo`); flat-at-3 ⇒ `γ|_{G₃}∈{1,χ₃|_{G₃}}` and, crucially, the extension is
  *peu ramifiée* ⇒ orientation fixed. Global characters unramified outside {2,3}, unramified at 2,
  into `k^×`: only `{1, χ₃}` (ℚ(ζ₃) is the sole quadratic field unramified outside 3; nothing
  unramified everywhere by Minkowski, `abs_discr_gt_two`). **Sub-case (i)** `γ=1`: trivial quotient
  ⇒ DONE. **Sub-case (ii)** `γ=χ₃` (trivial *sub*, orientation reversed): must be **excluded**;
  reduces to vanishing of the hardly-ramified (peu-ramifiée-at-3, unramified-at-2) Selmer class in
  `H¹(G_ℚ,χ₃)`. *This is the orientation counterexample; genuinely needs a proof, not Odlyzko.*
- **C3 (irreducible).** This case is **vacuous** — the goal (an ∃) is discharged by deriving a
  contradiction (`absurd`/`False.elim`), so no quotient need be exhibited. Steps:
  - **C3a Projective image.** `proj ρ: G_ℚ→PGL(2,k̄)` has finite image `G`. Dickson: `G∈
    {cyclic, dihedral, A₄, S₄, A₅}` (Borel/cyclic ⇒ reducible, excluded by C1). PSL2 simplicity
    `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple` exists but the *subgroup classification*
    does not.
  - **C3b Cut-out field.** `K := (K̄)^{ker(proj ρ)}`, a number field, `Gal(K/ℚ)≅G`, unramified
    outside {2,3}, `[K:ℚ]=|G|`.
  - **C3c Archimedean signature.** `det ρ(c)=χ₃(c)=−1` ⇒ `c` acts nontrivially ⇒ `K` totally complex
    (`IsTotallyComplex`, `TotallyRealComplex.lean:209`).
  - **C3d Ramification/discriminant UPPER bound.** tame-at-2 bounds `v₂`-contribution; flat-at-3
    (finite-flat group scheme over `ℤ₃`, wild but bounded exponent) bounds `v₃`-contribution ⇒
    `rootDiscr K < 8.25` (indeed `< 9.3`). **This bound is the missing Fontaine/Serre input.**
  - **C3e Numerical contradiction.**
    - `|G| ≥ 18` (`S₄`=24, `A₅`=60): `Odlyzko_statement` ⇒ `rootDiscr K ≥ 8.25`, contradicting C3d.
    - `|G| < 18` (`A₄`=12; small dihedral): needs small-degree minima (missing). Dihedral =
      induced from a quadratic subfield ⇒ separately reduces to a character argument (CM/induced),
      often folded into C2.
  - So exactly `{A₄, S₄, A₅}` (+ dihedral handled by induction to characters) are the "exceptional"
    cases genuinely needing discriminant arithmetic; `S₄,A₅` via Odlyzko, `A₄` via a deg-12 minimum.
- **C4 Join.** In every case produce (or vacuously obtain) the invariant trivial quotient `π`; export
  to the exact `mod_three` conclusion (§4 join theorem), transporting orientation faithfully.

Cases needing genuinely separate treatment: **C0** (coefficient descent), **C2(ii)** (Selmer
orientation), **C3a/b/d** (classification + cut-out + upper bound infrastructure), **C3e small-degree**.

---

## 4. DEPENDENCY GRAPH (transitively reduced) + JOIN

```
FLT-HR-DEF (proved)
   │ definition
   ▼
[N0 Odlyzko_statement]  [N1 flatDiscBound]  [N2 smallDiscMinima]  [N3 PGL2 Dickson class.]   (named historical axioms)
        \            \              |              /                 /
         \            \             |             /                 /
   L0 charThree ── L1 dichotomy ── L2 reducibleTrivialQuotient(+SelmerVanish) ── L3 cutOutField ── L4 totallyComplex ── L5 rootDiscUpper ── L6 numericContradiction
                                     \______________________________ ⇒ ______________________________/
                                                              │
                                                              ▼
                              modThree_classification_core   (FLT-FONTAINE-ODLYZKO, T2)
                                                              │ theorem (join, orientation-preserving)
                                                              ▼
                              GaloisRepresentation.IsHardlyRamified.mod_three   (FLT-MOD3, T1 export)
```

**Join theorem (exports the exact `mod_three` conclusion unchanged):**

```lean
theorem mod_three_of_core
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
      ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v :=
  FLT.HardlyRamified.modThree_classification_core hV hρ
```

The core's conclusion type is chosen to be **definitionally the same existential** so the join is a
one-liner and does not weaken/reorient `mod_three`.

---

## 5. PROPOSED LEAN SIGNATURES (dependency order; elaboration-ready)

Namespace/module note: control decl is `FLT.HardlyRamified.modThree_classification_core` but the
consumer sits in `GaloisRepresentation.IsHardlyRamified` and the expected module is
`FLT.GaloisRepresentation.HardlyRamified.ModThreeCore`. **Recommend** placing the core in module
`FLT.GaloisRepresentation.HardlyRamified.ModThreeCore`, namespace
`GaloisRepresentation.IsHardlyRamified`, decl `modThree_classification_core`, and updating the control
`lean_declaration` string to match (metadata-only change proposed, not made here).

```lean
-- L0  (NEW, produced, kernel-clean; first slice)  char 3 is forced by finiteness + ℤ_[3]-algebra
theorem charThree_of_finite_algebra
    (k : Type u) [Finite k] [Field k] [Algebra ℤ_[3] k] : CharP k 3

-- Coefficient family fact used by C0
noncomputable def kAsGaloisField (k : Type u) [Finite k] [Field k] [CharP k 3] :
    Σ r : ℕ, k ≃+* GaloisField 3 (r+1)          -- via algEquivGaloisField

-- L1  (NEW)  irreducibility dichotomy specialised to the mod-3 hardly-ramified hypothesis
theorem dichotomy
    {k V} [Finite k] [Field k] [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ρ.IsIrreducible ∨ (∃ π : V →ₗ[k] k, Function.Surjective π ∧ ∀ g v, π (ρ g v) = π v)

-- N-axioms (named historical inputs; each pre-1990, none is the mod-3 classification)
axiom flatDiscBound        -- N1 Fontaine/Serre finite-flat + tame root-discriminant UPPER bound
    {K} [Field K] [NumberField K] (hK : /- unramified outside {2,3}, tame@2, flat@3 witness -/ ) :
    NumberField.rootDiscr K < (8.25 : ℝ)
axiom smallDiscMinima      -- N2 totally-complex disc minima for 2 ≤ n < 18 (Odlyzko/Diaz y Diaz)
    {K} [Field K] [NumberField K] [IsTotallyComplex K]
    (hn : 2 ≤ finrank ℚ K) (hn' : finrank ℚ K < 18) :
    NumberField.rootDiscr K ≥ (8.25 : ℝ)          -- table value; ≥ 8.25 suffices to clash with N1
-- N3 Dickson: finite subgroups of PGL₂ over a finite field (cyclic/dihedral/A₄/S₄/A₅/Borel)
--    stated as an inductive/classifying predicate on `Subgroup (PGL 2 k̄)`; interface TBD by review.
-- N0 = existing FLT.Odlyzko_statement (FLT/Assumptions/Odlyzko.lean:58), unchanged.

-- L2  (NEW)  reducible ⇒ trivial quotient (includes Selmer orientation exclusion of C2(ii))
theorem reducibleTrivialQuotient … (hred : ¬ ρ.IsIrreducible) (hρ …) :
    ∃ π : V →ₗ[k] k, Function.Surjective π ∧ ∀ g v, π (ρ g v) = π v

-- L3–L6  (NEW)  irreducible ⇒ False  (uses N0,N1,N2,N3 + C3a–e; cut-out field, totally complex,
--                                       rootDisc upper bound, numeric clash)
theorem irreducibleAbsurd … (hirr : ρ.IsIrreducible) (hρ …) : False

-- CORE  (NEW, T2)  the produced classification
theorem modThree_classification_core
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π), ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v :=
  (dichotomy hV hρ).elim
    (fun hirr => absurd (irreducibleAbsurd hV hirr hρ) not_false)   -- vacuous C3
    (fun h => h)                                                     -- C2 provides the quotient
```

Pseudo-Lean avoided for the buildable slice (L0, join, core skeleton). `flatDiscBound`,
`smallDiscMinima`, and the Dickson predicate are stated at interface level; their exact binders are
flagged as **review-open** because they depend on a finite-flat/cut-out API that does not yet exist.

---

## 6. LIBRARY MATCHES (pinned tree; exact locator or NONE FOUND)

| Node | Closest pinned declaration | Verdict |
|---|---|---|
| char-3 derivation | `charP_of_injective_algebraMap` `Mathlib/Algebra/CharP/Algebra.lean:24`; `charP_of_card_eq_prime_pow` `.../CharAndCard.lean:86` | EXACT building blocks |
| all finite fields `𝔽_{3^r}` | `GaloisField` `Mathlib/FieldTheory/Finite/GaloisField.lean:70`; `algEquivGaloisField:209` | EXACT |
| irreducibility | `GaloisRep.IsIrreducible` `FLT/Deformations/RepresentationTheory/GaloisRep.lean:404`; `Representation.IsIrreducible` `Mathlib/RepresentationTheory/Irreducible.lean:30`; Schur `:60` | EXACT |
| sub/quotient reps | `Subrepresentation` `Mathlib/RepresentationTheory/Subrepresentation.lean:31`; `IntertwiningMap.ker/range` `Intertwining.lean:125` | ADAPTABLE |
| cyclotomic character | `cyclotomicCharacter` `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` | EXACT (already used in Defs) |
| discriminant / root disc | `NumberField.discr` `Discriminant/Defs.lean:36`; `NumberField.rootDiscr` `Discriminant/Basic.lean:78` | EXACT |
| Minkowski/Hermite | `abs_discr_gt_two` `Discriminant/Basic.lean:274`; `abs_discr_ge_of_isTotallyComplex:224` | EXACT (weaker than Odlyzko) |
| totally complex | `IsTotallyComplex` `TotallyRealComplex.lean:209` | EXACT |
| PGL/PSL/SL₂ objects | `PGL(n,R)` `Matrix/GeneralLinearGroup/Projective.lean:41`; `PSL` `ProjectiveSpecialLinearGroup.lean:33`; `SpecialLinearGroup.toPGL:100`; PSL2 simple `Projectivization/PSL/PSL2.lean:120` | OBJECTS EXACT |
| **Dickson subgroup classification** | — | **NONE FOUND** |
| **finite-flat group scheme / disc bound** | planned `FLT.GroupScheme.FiniteFlat` (sorry) `FLT/KnownIn1980s/EllipticCurves/Flat.lean`; `GaloisRep.IsFlatAt` `GaloisRep.lean:391` (predicate only) | **NONE FOUND (bound); predicate exists** |
| **Odlyzko lower bound** | `FLT.Odlyzko_statement` `FLT/Assumptions/Odlyzko.lean:58` (axiom; deg ≥ 18 only) | AXIOM, PARTIAL |
| **small-degree disc minima** | — | **NONE FOUND** |
| flat/unramified predicates | `GaloisRep.IsFlatAt:391`, `GaloisRep.IsUnramifiedAt:316` | EXACT (carriers) |
| Brauer–Nesbitt / trace | `FLT/Components/Contracts/BrauerNesbitt.lean:45,86` | ADAPTABLE (for downstream three_adic, not here) |

`library-matches.ndjson:23` `MISS-011` already records this as `missing-interface`. Aspirational
names in the control row (`FiniteFlatGroupScheme`, `PGL2 finite subgroup classification`) are **not**
present — they must be produced or axiomatized, not cited.

---

## 7. COUNTEREXAMPLES AND FAILURE MODES (all hostile checks addressed)

1. **Non-prime finite coefficient field.** `k=𝔽_{3^r}`, r>1: the projective-image/Dickson analysis
   runs over `k̄=𝔽̄₃`; the invariant line must be **Frobenius-descended** to `k` (C0). Failure mode:
   proving existence only over `k̄` does not satisfy `π : V →ₗ[k] k`. Mitigation: descent lemma; if
   descent is skipped the theorem is *not covered for r>1*, violating the completion gate.
2. **`Algebra ℤ_[3] k` vs actual char 3.** No `[CharP k 3]` is given. If one silently *assumes*
   char 3 the proof is unsound for exotic `k`; but `[Finite k]` forces it (L0). Must be a real lemma,
   not an instance assumption. (Note Defs.lean also omits the `IsLocalHom` residue-char hypothesis,
   line 98 commented out — safe here because finiteness recovers it.)
3. **Reducible but non-split.** `0→𝟙→V→χ₃→0` (trivial sub, `χ₃` quotient) is hardly-ramified-shaped
   and has **no trivial quotient** ⇒ would falsify `mod_three`. Must be excluded by
   peu-ramifiée-at-3 + unramified-at-2 Selmer vanishing (C2(ii)). **This is the sharpest failure
   mode and is currently unproven.**
4. **Invariant subspace vs quotient orientation.** The conclusion is a *quotient* (`π` surjective,
   `π(ρ g v)=π v`). Dualizing a trivial *sub* gives a trivial quotient of `V^*`, not `V`. The proof
   must land the trivial factor on TOP of `V`; flatness-at-3 (peu ramifiée) is what fixes this.
5. **Projective vs linear image.** Dickson classifies `PGL₂` image; lifting to `GL₂` adds a
   central/character twist. The cut-out field uses the *projective* image (degree `|G|`); using the
   linear image degree would give wrong `n` and mis-apply Odlyzko.
6. **Real vs totally complex cut-out field.** Odlyzko/`smallDiscMinima` require `IsTotallyComplex`.
   If C3c (from `χ₃(c)=−1`) is not established, the bound does not apply — the argument collapses.
   Totally-*real* fields have different (smaller) minima.
7. **Discriminant bound insufficient to force the group case.** `Odlyzko_statement` only fires for
   `n≥18`. `A₄` (n=12) and small dihedral fields are **not** excluded by it ⇒ need `smallDiscMinima`
   (N2). Silent reliance on N0 alone leaves a real gap (design finding driving the `UNCERTAIN`).
8. **Accidental use of the desired classification as an assumption.** Any node whose hypothesis is
   "ρ is reducible" or "ρ has a trivial quotient", or any use of `knownin1980s` to discharge the core
   or of `HardlyRamifiedReducibilityContract` (which is `ℓ≥5` only, `Scaffold.lean:32`) for `ℓ=3`,
   is **circular** and forbidden. The scaffold's `5 ≤ ell` guard confirms the mod-3 branch may not
   borrow the generic reducibility.

---

## 8. FIRST BUILDABLE SLICE (kernel-clean; retires a real edge)

**Slice A — coefficient-field foundation + orientation-preserving join.** Module
`FLT.GaloisRepresentation.HardlyRamified.ModThreeCore`.

Imports: `FLT.GaloisRepresentation.HardlyRamified.Defs`, `Mathlib.Algebra.CharP.Algebra`,
`Mathlib.FieldTheory.Finite.GaloisField`.

Deliverables (all provable now, no new axioms):
1. `charThree_of_finite_algebra (k) [Finite k][Field k][Algebra ℤ_[3] k] : CharP k 3` — via the
   `ℤ_[3]→k` kernel argument / `charP_of_injective_algebraMap` contrapositive. **Retires the
   coefficient-coverage half of the completion gate.**
2. `kAsGaloisField` witness that every such `k` is `𝔽_{3^r}` (`algEquivGaloisField`).
3. A **stated** `modThree_classification_core` whose *conclusion is definitionally equal* to
   `mod_three`'s, with body reduced to `dichotomy`/`irreducibleAbsurd`/`reducibleTrivialQuotient`
   (initially `sorry`), plus the **join `mod_three_of_core`** proved as a one-liner from the core.

Completion audit for Slice A: `#print axioms charThree_of_finite_algebra` must show only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `knownin1980s`); the join must add no
axioms beyond the core's. This is exactly the kind of pin already used in
`methodology/evidence/contracts/ExistingAdaptersAudit.lean` (`#guard_msgs in / #print axioms`).
Slice A **retires edge `E-HR-DEF-FONTAINE-ODLYZKO`'s coefficient obligation** and makes
`E-FONTAINE-ODLYZKO-MOD3` a checked one-liner, without touching the two open soundness questions.

Do **not** proceed past Slice A into L2–L6 until the §9 gate is cleared.

---

## 9. STOP-LOSS GATE

Halt and re-authorize before implementing anything beyond Slice A if **any** of the following holds:

- **G1 (axiom-boundary).** The operator has not authorized T2 to introduce `flatDiscBound` (N1),
  `smallDiscMinima` (N2), and a Dickson `PGL₂` classification (N3) as *additional* named pre-1990
  axioms alongside `Odlyzko_statement`. As shown, N0 alone cannot close the classification. Building
  L3–L6 against undefined/undocumented axioms, or discharging the core via `knownin1980s`, would
  "hide the classification behind a renamed assumption" — forbidden.
- **G2 (statement soundness).** The reducible non-split orientation (C2(ii)) is not yet excluded. If
  a hardly-ramified `0→𝟙→V→χ₃→0` with no trivial quotient exists, `mod_three` **as currently stated
  is false** and must be restated (e.g. "trivial quotient OR trivial sub", changing the downstream
  `three_adic` contract). Do not build L2 until this is settled by proof, not citation.
- **G3 (infrastructure).** No finite-flat group-scheme→discriminant API exists; if `flatDiscBound`
  cannot even be *stated* with existing predicates (the cut-out field + flat witness), the T2 route
  is not expressible and the component must be **decomposed** into a prerequisite "cut-out field /
  root-disc estimate" obligation first.
- **G4 (source).** If Poitou 1977 p.17 / Serre 1987 §4 on re-inspection do not actually supply the
  *upper* bound (N1) or the small-degree minima (N2) in a pre-1990 form, those axioms are not
  "historical" and the boundary is illegitimate at T2.

Past this gate the design is **not** to be implemented without operator sign-off.

---

## 10. DEFINITION OF READY (component checklist)

| DoR field (`source-design.ndjson:20`) | State after this design | Evidence |
|---|---|---|
| `primary_source_exact` | **true** (was true) | SRC-003, SRC-005, SRC-007 located; N1/N2 locators flagged unresolved |
| `hypothesis_translation` | **partial** | `IsHardlyRamified` fields ↔ det/unram/flat/tame mapped; char-3 derivation specified |
| `proof_outline` | **true (route), gated** | §3 case graph C0–C4 complete; gated by G1–G4 |
| `sublemma_graph` | **true** | §4 reduced graph + join; L0–L6, N0–N3 |
| `counterexample_review` | **true** | §7 all 8 hostile checks addressed; two unresolved (C2(ii), small-degree) named |
| `library_matches` | **true** | §6 exact locators / NONE FOUND, incl. MISS-011 |
| `lean_signature` | **partial** | Slice-A signatures elaboration-ready; L2–L6/N-axiom binders review-open |
| `dor` | **remains BLOCKED** | pending G1–G4 resolution + Slice-A kernel probe |

Component is **NOT** Definition-of-Ready. Slice A is ready to build; the classification core is not.

---

## 11. OPEN QUESTIONS FOR GPT-5.6 xhigh REVIEW / OPERATOR

1. **Is the expanded T2 axiom set authorized?** Specifically N1 `flatDiscBound` (Fontaine/Serre),
   N2 `smallDiscMinima` (Odlyzko/Diaz y Diaz small-degree), N3 Dickson `PGL₂` classification —
   each pre-1990, none the mod-3 classification itself. Or must the component be **decomposed** so
   each becomes its own obligation with a source audit?
2. **C2(ii) orientation / `mod_three` correctness.** Confirm (or refute) that flat-at-3 ⇒
   peu-ramifiée ⇒ the trivial factor is forced onto the quotient, so no hardly-ramified
   `0→𝟙→V→χ₃→0` exists. If it can exist, the *statement* `mod_three` needs revision — a T1 change
   with `three_adic` knock-on.
3. **Exact `flatDiscBound` binder.** What witness of "unramified outside {2,3} + tame@2 + flat@3"
   should the cut-out field carry, given no finite-flat API exists? Should the cut-out-field
   construction (C3b) be its own prerequisite obligation?
4. **Small-degree numeric thresholds.** What precise deg-12 (and small-dihedral) totally-complex
   root-discriminant minima from the pre-1990 tables clash with the C3d upper bound? Confirm the
   `8.25` upper bound (vs `9.3`) leaves margin against every surviving `A₄`/dihedral field.
5. **Namespace/decl reconciliation.** Approve moving the core to namespace
   `GaloisRepresentation.IsHardlyRamified`, module `…HardlyRamified.ModThreeCore`, and updating the
   control `lean_declaration` string accordingly.

## 12. VERIFICATION (read-only, only when authorized to build Slice A)
- `lake build FLT.GaloisRepresentation.HardlyRamified.ModThreeCore`
- `#print axioms charThree_of_finite_algebra` ⇒ expect `[propext, Classical.choice, Quot.sound]`.
- `#print axioms mod_three_of_core` ⇒ adds nothing beyond `modThree_classification_core`.
- Re-`#check GaloisRepresentation.IsHardlyRamified.mod_three` unchanged type
  (`FLTMethodology/Probes/ExistingContracts.lean:25`).
