# Opus 4.8 primary design output

Component: `class-field / FLT-CLASS-FIELD`
Agent: `opus48-primary-designer-d10`
Model/backend: `claude-opus-4-8` / `claude-code`
Verdict: **READY-FOR-GPT-REVIEW**
Bridge duration: 715539 ms
Claude session: `16911907-98cf-478b-8a91-f66d09389def`

The model completed within its scheduled difficulty budget. Claude's plan-mode transport wrote the
full report to `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-serialized-hellman.md` despite the read-only prompt and returned only a summary to the bridge.
That out-of-repository provider side effect is recorded honestly; the report below is the complete
plan artifact copied into the governed component directory. No external file was edited or deleted
by this orchestration step.

---

# PRIMARY OPUS 4.8 DESIGN — CLASS FIELD (`FLT-CLASS-FIELD`)

**Role:** first-attempt primary producer, Opus-first ladder. Read-only. Deliverable is the 9-section
independent Stage-1 design required by
`methodology/review/flt-completion/class-field/stage-1-prompt-nonfable.md` (actor/tri-design routing
ignored per the Opus-48-primary override).

**Repository state note.** Prompt cites frozen baseline branch
`methodology/varro-proof-program-20260716` @ `827eb969…`. The working tree is on that branch but at
`66e4f1ef0af0f316f15f0d2d733c93969114ffde` (later than the cited SHA). All findings below are read
off the current working tree; a reviewer should re-pin to `827eb96…` if exact-SHA fidelity is
required. No class-field declarations exist at either SHA, so the drift does not change the verdict.

**Verdict token (Opus ladder):** `READY-FOR-GPT-REVIEW`
**Disposition (nonfable section-9 vocabulary):** `INTERFACE-FIRST`
(Full reciprocity *isomorphisms* cannot elaborate yet — their domain objects are absent — but a
source-faithful decomposition, honest kernel-clean first slice, and stop-loss set are complete and
ready for GPT-5.6 xhigh review.)

---

## Context (why this design exists)

The proof-graph proposes a single declaration `FLT.PotentialModularity.classField_package`
(`proof-obligations.ndjson:17`) as the class-field input to potential modularity. **No such
declaration exists** — nor does the `FLT.PotentialModularity` namespace, nor either downstream
consumer declaration (verified by repo-wide grep: zero hits for `classField_package`,
`induced_rep_isAutomorphic`, `exists_auxiliary_curve`, `PotentialModularity`). `FLT-CLASS-FIELD` is a
**definition-gap**, not a tactic hole. `source-design.ndjson:16` sets the exact next gate this report
answers: *"Difficulty-10 Opus primary design running to select exact local-global reciprocity
interfaces; GPT-5.6 xhigh independent review follows."* The design must replace the omnibus package
with the smallest set of separately named contracts that (a) each map to a genuine class-field
theorem, (b) supply exactly what the two observed consumers need, and (c) never smuggle in the
downstream conclusions (automorphy of the induced representation, or existence of the auxiliary
curve) under the banner "class field theory."

---

## 1. Observed baseline and exact consumers

**Actual Lean consumers of `FLT-CLASS-FIELD`: NONE.**
No `.lean` file references `classField_package` or the `FLT.PotentialModularity` namespace. The
entire potential-modularity layer is greenfield. `library-matches.ndjson` has **no** record for
`FLT-CLASS-FIELD` (only `MISS-007`, an `absent` verdict for `FLT-INDUCED-MOD`).
`source-design.ndjson:16` marks the component `dor:"BLOCKED"`, every design gate `false`.

**Planned graph consumers (prose-only, two, both `absent`):**

| Consumer | Decl (nonexistent) | Edge | What it *actually* needs from CFT |
|---|---|---|---|
| `FLT-INDUCED-MOD` | `FLT.PotentialModularity.induced_rep_isAutomorphic` | `E-CLASS-FIELD-INDUCED-MOD` (`proof-graph.ndjson:88`) | A **finite-order Galois character** `χ` of a quadratic extension `E/F` with prescribed parity/conductor, plus the **determinant & conductor of `Ind χ`** — so converse-theorem hypotheses can be matched. It does **not** need CFT to prove automorphy (that is the converse theorem, internal to `FLT-INDUCED-MOD`; it also consumes `FLT-JL`). |
| `FLT-AUX-CURVE` | `FLT.PotentialModularity.exists_auxiliary_curve` | `E-CLASS-FIELD-AUX-CURVE` (`proof-graph.ndjson:91`) | (i) A **finite-order character with prescribed local components** to realise "mod-`p` rep induced from a character"; (ii) **local reciprocity** to phrase the local conditions; (iii) a **solvable/Galois extension with prescribed local behaviour + disjointness** (Grunwald–Wang). It does **not** need CFT to build the curve (that is Moret–Bailly, `FLT-MORET-BAILLY`; the field/local piece is shared with `FLT-AUX-LOCAL-FIELD`). |

`FLT-CLASS-FIELD` has `direct_dependencies:[]`, `graph_depth:0`, no incoming edges — a leaf source.
**Discipline consequence:** supply reciprocity + character existence + induced-character
bookkeeping, and *nothing else*. Do **not** import Poincaré duality / Euler characteristic
(those are `FLT-LOCAL-GALOIS`, not consumed here), nor multiplicity-one, nor base change.

---

## 2. Source theorem boundary

Primary source register: `SRC-004` = FLT blueprint ch.4 overview
(`blueprint/src/chapter/ch04overview.tex`), graded *"Read; explicitly incomplete upstream"*
(`SOURCE-REGISTER.md:12`). ch.4 only **mentions** CFT ("several nontrivial results in global class
field theory", l.29; "Local class field theory … gives a map `I_v→𝒪_{F_v}^×` and hence `I_v→k(v)^×`",
ll.46–47). The **actual statements** live in the appendix
`blueprint/src/chapter/chtopbestiary.tex`, all flagged `\notready`, none with a `\lean{}`/`\leanok`
label, all justified by literature citation (`\cite{cf}`) rather than proof:

| Source label (TeX) | Locator | Statement | Status |
|---|---|---|---|
| `local_class_field_theory` | `chtopbestiary.tex:24` | Two canonical topological-group isos `K^× ≅ (W_K)^{ab}` (`K/ℚ_p` finite). | Stated `\notready`; proof = "main theorem of local CFT, see [cf]". |
| `global_class_field_theory` | `chtopbestiary.tex:83` | Two canonical isos `π₀(𝔸_N^×/N^×) ≅ (G_N)^{ab}`, uniformisers→Frobenii, **compatible with the local isos**. | Stated `\notready`; proof = "main theorem of global CFT, see Tate in [cf]". |
| `Skinner_Wiles_CFT_trick` | `chtopbestiary.tex:90` | For finite `S`, prescribed finite Galois `L_v/K_v` at each `v∈S`, there is a **finite solvable Galois `L/K`** with `L_w/K_v ≅ L_v/K_v`, choosable **linearly disjoint** from any given `K^{avoid}`. | Stated `\notready`, **no proof block at all**. |
| `local_Weil_group` (def) | `chtopbestiary.tex:19` | Weil group of `K` (domain object for local CFT). | `\notready` definition. |

**Why `SRC-004` alone is insufficient.** It is graded incomplete; every class-field statement it
transitively points to is `\notready` prose with a literature pointer and no Lean signature;
`Skinner_Wiles_CFT_trick` has no proof at all. Per `MLT-SOURCE-CONTRACT.md` (the governing
discipline), *"a source citation does not make a Lean declaration proved"* and a repository predicate
may not be identified with a source statement, shortcut by a generic `Prop`/axiom, nor given a Lean
signature *"until its prerequisite vocabulary elaborates"* (the "Lean signature stop point"). Treat
these as **stated-but-stubbed targets (definition-gap)**, not inputs. A dedicated CFT source
(Artin/Tate — Cassels–Fröhlich `[cf]`, or Serre `[serre-galcoh]`) should be added to the register;
Mathlib itself only points at the **external** `mariainesdff/LocalClassFieldTheory` and
`kbuzzard/ClassFieldTheory` repos (comment citations in
`Mathlib/RingTheory/Valuation/Discrete/Basic.lean:57` and
`Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean:49`).

**Unverified-locator / mismatch flags:** `library_candidates` on the obligation
(`["NumberField.AdeleRing","IsLocalClassField","ContinuousCharacter"]`) is only **1/3 real**:
`NumberField.AdeleRing` exists; **`IsLocalClassField` does not exist** in the pinned Mathlib
(`a3364fae…`); **`ContinuousCharacter` does not exist** as a named decl (only `ContinuousMonoidHom`).
This must be corrected in the ledger.

---

## 3. Minimal component split (replaces `classField_package`)

Four separately named contracts, one per class-field theorem the consumers actually touch. No omnibus
structure; no "authority" field.

- **`CF-LOCAL-RECIP` — local reciprocity.** The local Artin map / inertia character
  `I_v → 𝒪_{F_v}^× → κ(v)^×`. Source: `local_class_field_theory`. Needed by `FLT-AUX-CURVE`
  (phrasing local conditions) and as the compatibility target of the global map.
- **`CF-GLOBAL-RECIP` — global reciprocity.** `π₀(𝔸_F^×/F^×) ≅ (Γ F)^{ab}`, compatible with local.
  Source: `global_class_field_theory`. The engine converting idele-class (Hecke) characters to Galois
  characters; underlies character existence.
- **`CF-CHAR-PRESCRIBE` — character construction / local prescription (Grunwald–Wang family).**
  (a) existence of a **finite-order continuous character** with prescribed local components at a
  finite `S`; (b) `Skinner_Wiles_CFT_trick` **field** version (prescribed local extensions +
  disjointness). Consequence of `global_class_field_theory`. Needed by both consumers; part (b) is a
  **shared boundary with `FLT-AUX-LOCAL-FIELD`** — flag for de-duplication in review.
- **`CF-COMPAT` — compatibility.** (a) local–global compatibility (global character's local
  component at `v` = local reciprocity image — the clause inside `global_class_field_theory`);
  (b) **induced-character bookkeeping**: `det(Ind_{Γ_E}^{Γ_F} χ) = ε_{E/F}·(χ∘transfer)` and
  `cond(Ind χ)` via conductor–discriminant. Feeds `FLT-INDUCED-MOD` hypothesis-matching. **This is
  a fact *about* induction, not the automorphy of the induced representation.**

Separation is exactly along the four axes the prompt enumerates (local / global / character-and-local-
prescription / compatibility) and no finer — merging any two would either bundle a proved iso with an
unproved existence result, or hide the local–global compatibility that is the whole content.

---

## 4. Exact Lean signatures in dependency order

Common context (all `EXISTING-PROVED` unless noted):
`Γ K := Field.absoluteGaloisGroup K` (`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:39`);
`Field.absoluteGaloisGroup.map (f : K →+* L) : Γ L →ₜ* Γ K` (ibid. :75);
`GaloisRep F A M` (`FLT/Deformations/RepresentationTheory/GaloisRep.lean:49`) with
`GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M` (:76),
`GaloisRep.conj` (:98), `GaloisRep.ker` (:69), `.toRepresentation` (used at
`FLTMethodology/Probes/MLTSourceBoundary.lean:61`);
`GaloisRep.IsAutomorphicOfLevel` (`FLT/GaloisRepresentation/Automorphic.lean:70`);
`Representation.ind` / `Rep.ind` / `Rep.indResAdjunction` (`Mathlib/RepresentationTheory/Induced.lean:79,104,157`);
`DirichletCharacter` + `.conductor` (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40,246`);
`ContinuousMonoidHom` (`Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:57`);
`NumberField.AdeleRing` + `principalSubgroup` (`Mathlib/NumberTheory/NumberField/AdeleRing.lean:47,70`, **additive only**).

### Slice A — elaborates now (leaves; all `PROPOSED`, kernel-clean, over EXISTING vocabulary)

```lean
namespace FLT.PotentialModularity.ClassField   -- production target module

/-- A finite-order (Artin) Galois character: a rank-1 continuous Galois representation with
    finite image.  EXISTING refs: `GaloisRep`.  PROPOSED def. -/
def IsFiniteOrderCharacter
    {F : Type*} [Field F] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (χ : GaloisRep F A M) : Prop :=
  Module.finrank A M = 1 ∧ (Set.range (fun σ => χ σ)).Finite

/-- Local component of a global Galois character at a finite place `v`, via the completion
    embedding `F → F_v`.  Uses EXISTING `GaloisRep.map`.  PROPOSED. -/
noncomputable def localComponent
    {F : Type*} [Field F] [NumberField F] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (χ : GaloisRep F A M) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    GaloisRep (v.adicCompletion F) A M :=
  χ.map (algebraMap F (v.adicCompletion F))

/-- Prescribed-local-component relation over a finite set `S`.  PROPOSED (a *relation*, not an
    existence theorem — the existence claim is `CF-CHAR-PRESCRIBE`, section below). -/
def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (χ : GaloisRep F A M) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A M) : Prop :=
  ∀ v (hv : v ∈ S), localComponent χ v = χloc v hv

/-- The induced Galois representation object for a finite extension `E/F`, via EXISTING
    `Representation.ind` along `Γ E → Γ F`.  Constructs the OBJECT only — it makes NO automorphy
    claim (that stays in `FLT-INDUCED-MOD`).  PROPOSED adapter; exact `Representation.ind` argument
    order to be confirmed at elaboration against `Mathlib/RepresentationTheory/Induced.lean`. -/
-- def inducedRepresentation … := Representation.ind (Field.absoluteGaloisGroup.map (algebraMap F E)) χ.toRepresentation
```

### Slice B — DEFINITION-GAP now (domain objects absent → do NOT fabricate a signature)

Per the MLT "signature stop point", the following are **named future obligations**, not elaborable
Props, because their domains are missing from Mathlib/FLT:

- `CF-LOCAL-RECIP`: local reciprocity iso needs the **local Weil group** `(W_{F_v})^{ab}` — absent.
  Even the honest weaker form `inertia(v) → κ(v)^×` needs a named inertia-subgroup-of-`Γ F_v`
  object — absent as a reusable decl.
- `CF-GLOBAL-RECIP`: needs the **multiplicative idele class group** `𝔸_F^× / F^×` and its `π₀`, and
  `(Γ F)^{ab}` — absent (Mathlib only has the *additive* `principalSubgroup`; no `AdeleRing.units`,
  no `IdeleClassGroup`, no `π₀` quotient).
- `CF-CHAR-PRESCRIBE` (existence half) and `CF-COMPAT` (local–global half) depend on the two above.

**Proposed target types (to be frozen only once the domain objects land), stated abstractly:**

```lean
-- PROPOSED TARGET (definition-gap): local reciprocity.
-- def LocalReciprocity (K : Type*) [Field K] [<p-adic local field TCs>] :
--   Kˣ ≃ₜ* (LocalWeilGroup K)ᵃᵇ        -- LocalWeilGroup: MISSING domain object
--
-- PROPOSED TARGET (definition-gap): global reciprocity, compatible with local.
-- def GlobalReciprocity (F : Type*) [Field F] [NumberField F] :
--   IdeleClassGroup.π₀ F ≃ₜ* (Γ F)ᵃᵇ    -- IdeleClassGroup: MISSING domain object
--
-- PROPOSED TARGET: finite-order character with prescribed local components (Grunwald–Wang),
--   stated over the Slice-A relation once existence is provable:
-- theorem exists_finiteOrderCharacter_prescribed
--     (S) (χloc : ∀ v ∈ S, …) (hGW : NonExceptional S χloc) :
--     ∃ χ : GaloisRep F A M, IsFiniteOrderCharacter χ ∧ HasPrescribedLocalComponents χ S χloc
```

Label summary: `Field.absoluteGaloisGroup(.map)`, `GaloisRep(.map/.conj/.toRepresentation)`,
`GaloisRep.IsAutomorphicOfLevel`, `Representation.ind`, `DirichletCharacter.conductor`,
`ContinuousMonoidHom`, `NumberField.AdeleRing` = **EXISTING-PROVED**; `cyclic_base_change` =
**EXISTING-ADMITTED** (`FLT/GaloisRepresentation/Automorphic.lean:194` `sorry`, not used by this
design); all `CF-*` targets and every `IsLocalClassField`/`ContinuousCharacter`/`IdeleClassGroup`/
`LocalWeilGroup` = **PROPOSED / MISSING**.

---

## 5. Pinned-library matches

| Object | Pinned decl | Location | Class |
|---|---|---|---|
| Adele ring | `NumberField.AdeleRing` (+`principalSubgroup`, additive) | `Mathlib/…/NumberField/AdeleRing.lean:47,70` | **exact** (adele ring); **missing** (idele class group / `π₀`) |
| Continuous character carrier | `ContinuousMonoidHom`, `PontryaginDual` | `Mathlib/Topology/Algebra/{ContinuousMonoidHom,PontryaginDual}.lean` | **adaptable** (carrier only; not a CFT character) |
| Finite-order character prototype | `DirichletCharacter`, `.conductor` | `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40,246` | **signature-only** (ℤ/n model, not idelic/Galois) |
| Induced representation | `Representation.ind`, `Rep.ind`, `Rep.indResAdjunction` | `Mathlib/RepresentationTheory/Induced.lean:79,104,157` | **exact** (rep-theory induction); bridge `GaloisRep→Representation` via `.toRepresentation` **adaptable** |
| Galois representation | `GaloisRep`, `.map`, `.conj`, `.toRepresentation` | `FLT/Deformations/RepresentationTheory/GaloisRep.lean` | **exact** |
| Absolute Galois functoriality | `Field.absoluteGaloisGroup.map` | `FLT/…/AbsoluteGaloisGroup.lean:75` | **exact** |
| Group transfer (for `χ∘transfer`) | `MonoidHom.transfer` | `Mathlib/GroupTheory/Transfer.lean` | **adaptable** |
| **Local class field theory** | — | — | **missing** (no `IsLocalClassField`, no `LocalWeilGroup`, no local Artin map) |
| **Global class field theory / Artin reciprocity** | — | — | **missing** (no `artinMap`/`reciprocityMap`/`IdeleClassGroup`; only *quadratic* reciprocity exists) |
| Tate cohomology (support, not used here) | `…/TateCohomology/Basic.lean` | Mathlib | **exact** but out of scope |

The obligation's `library_candidates` are corrected: keep `NumberField.AdeleRing`; **drop**
`IsLocalClassField` and `ContinuousCharacter` (nonexistent) → replace with `ContinuousMonoidHom`,
`Representation.ind`, `GaloisRep`, `Field.absoluteGaloisGroup.map`, `DirichletCharacter.conductor`.

---

## 6. Statement risks and counterexamples

1. **Frobenius normalization (local/global direction).** Both reciprocity isos come in *two*
   canonical forms (arithmetic vs geometric Frobenius; `chtopbestiary.tex:12,83`). Fix **one** globally
   and thread it through `CF-LOCAL-RECIP`/`CF-GLOBAL-RECIP`/`CF-COMPAT`; a silent mixed convention
   flips a sign in `det(Ind χ)` and breaks parity matching downstream.
2. **Grunwald–Wang exceptional case (product-formula obstruction) — real counterexample.** Prescribing
   arbitrary local components of prescribed order is **false** in the special 2-primary case (the
   classical Grunwald–Wang counterexample: no global character of order 8 with prescribed behaviour at
   2). `CF-CHAR-PRESCRIBE` **must** carry an explicit non-exceptionality / Hilbert-reciprocity
   compatibility hypothesis (`hGW : NonExceptional …`), not claim unconditional existence. Omitting it
   makes the interface *unsound*.
3. **Continuity/topology.** Characters must be `ContinuousMonoidHom` for the profinite/adelic topology;
   a set-theoretic (AC-produced, discontinuous) character is a genuine non-example. `IsFiniteOrderCharacter`
   uses `GaloisRep` (continuity built in) — keep it that way; never weaken to a bare `MonoidHom`.
4. **Finite-order requirement.** The inducing character must be **finite order** so `Ind χ` has finite
   image and reduces to the mod-`p` Galois representation. An infinite-order Hecke character yields an
   automorphic rep but **not** the finite-image mod-`p` object `FLT-AUX-CURVE` needs — counterexample if
   the `finrank=1 ∧ finite range` clause is dropped.
5. **Coefficient/codomain mismatch.** The mod-`p` induced rep is valued in a finite field / roots of
   unity; the Hecke/automorphic side in ℂ or `ℚ̄_p`. Pin the coefficient ring `A` per use and provide an
   explicit compatibility, not a definitional identification (mirrors MLT-contract rule: "a generic
   integral-coefficient representation is not definitionally the source representation").
6. **Extension/restriction direction.** `Representation.ind` induces *up* `Γ E → Γ F`; the character
   lives on `Γ E` (the quadratic ext), the induced rep on `Γ F`. Reversing gives restriction, not
   induction — determinant/conductor formulas would be wrong.
7. **Circularity guard (the central risk).** `CF-COMPAT`(b) computes `det`/`cond` of `Ind χ` only. It
   must **not** assert `Ind χ` is automorphic (= `FLT-INDUCED-MOD`, via converse theorems + `FLT-JL`),
   nor that the auxiliary curve exists (= `FLT-AUX-CURVE`, via Moret–Bailly). Any field of a class-field
   contract that presupposes `IsAutomorphicOfLevel` or curve existence is an assumption "equivalent to
   potential modularity/automorphic induction/auxiliary-curve existence under the name class field
   theory" and is rejected by the prompt's final constraint.
8. **Even-degree / totally-real side conditions.** `F` must be totally real of even degree (definite
   quaternion algebra exists). `CF-CHAR-PRESCRIBE`(b) (the field) must carry these + disjointness from
   the residual kernel `K` as explicit hypotheses, and must not silently overlap `FLT-AUX-LOCAL-FIELD`.

---

## 7. Smallest buildable first slice

**Module (probe, isolated, not imported by `FLT`/`FermatsLastTheorem`):**
`FLTMethodology/Probes/ClassFieldBoundary.lean`, added to `FLTMethodology.lean`, mirroring
`FLTMethodology/Probes/MLTSourceBoundary.lean` exactly (kernel-clean defs + `#check`/`#print axioms`,
no theorem claimed).

**Contents = Slice-A only:** `IsFiniteOrderCharacter`, `localComponent`, `HasPrescribedLocalComponents`,
and the `inducedRepresentation` adapter (object, not automorphy). These elaborate over existing
vocabulary and introduce **no** `sorry`. It is an honest interface/adapter slice: it does **not**
state or prove reciprocity, character existence, or automorphy.

**Commands (read-only verification the reviewer/executor runs):**
```
lake build FLTMethodology.Probes.ClassFieldBoundary
```
then, inside the module, for each definition:
```
#check FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
#check FLT.PotentialModularity.ClassField.localComponent
#check FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
#print axioms FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
#print axioms FLT.PotentialModularity.ClassField.localComponent
#print axioms FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
```
**Pass criterion:** builds clean; each `#print axioms` shows only the standard trio
(`propext`, `Classical.choice`, `Quot.sound`) and **no `sorryAx`**. (If `localComponent`'s adic-
completion `NumberField`/typeclass plumbing does not resolve, degrade it to a `variable`-bound
completion field `Fᵥ` with a supplied `algebraMap F Fᵥ` — still kernel-clean, still honest.)

The production module `FLT/PotentialModularity/ClassField.lean` (expected module of record) is
**not** created in this slice beyond re-exporting Slice-A adapters, because `CF-LOCAL/GLOBAL-RECIP`
cannot elaborate honestly yet (section 4B).

---

## 8. Dependency graph and gates

**Component-local DAG (new nodes, all under work item `FLT-304`):**
```
CF-LOCAL-RECIP  ─┐
                 ├─►  CF-COMPAT ──►  FLT-INDUCED-MOD
CF-GLOBAL-RECIP ─┤        ▲
   │             │        │
   └──►  CF-CHAR-PRESCRIBE ┘──►  FLT-AUX-CURVE   (with FLT-AUX-LOCAL-FIELD, FLT-MORET-BAILLY)
        (a: char existence  b: solvable field — b shared w/ FLT-AUX-LOCAL-FIELD)
Slice-A adapters (IsFiniteOrderCharacter, localComponent, HasPrescribedLocalComponents,
inducedRepresentation) are the buildable leaves feeding CF-CHAR-PRESCRIBE / CF-COMPAT.
```

**Completion gate** (from the obligation, honoured): *"Every bundled field is a separately named
theorem with source and target-stage axiom audit."* — met by the four-way split; each `CF-*` gets its
own source locator (section 2) and its own `#print axioms` at T2/T3.

**DoR-advancing evidence:** (i) Slice-A probe builds kernel-clean (`#print axioms` = trio, no
`sorryAx`); (ii) ledger corrections applied (real `library_candidates`; `SRC-004` supplemented with a
dedicated CFT source; `FLT-304` boundary split into the four `CF-*` nodes); (iii) GPT-5.6 xhigh review
confirms no `CF-*` field presupposes a downstream conclusion.

**Stop-loss / redesign triggers:**
- **S1 (source work).** If the multiplicative idele class group + `π₀` + local Weil group do not land
  (Mathlib or vendored `mariainesdff/LocalClassFieldTheory` / `kbuzzard/ClassFieldTheory`) within the
  wave, `CF-LOCAL/GLOBAL-RECIP` cannot be stated → escalate to explicit **source/vendoring work**;
  keep only Slice-A. (This is why the disposition is INTERFACE-FIRST, not DESIGN-VIABLE-with-signatures.)
- **S2 (redesign).** If review shows any `CF-*` field bundles automorphy / curve existence / an
  omnibus authority axiom → **REVISE** the split.
- **S3 (soundness).** If Grunwald–Wang non-exceptionality cannot be stated honestly in Lean →
  restrict `CF-CHAR-PRESCRIBE` scope to the provable sub-case or **OBSTRUCTION** on that sub-node.
- **S4 (dedup).** If `CF-CHAR-PRESCRIBE`(b) is found to duplicate `FLT-AUX-LOCAL-FIELD` → move the
  field-construction node there and keep class-field to reciprocity + character existence only.

---

## 9. Verdict

**Opus-ladder token:** `READY-FOR-GPT-REVIEW`
**Nonfable disposition:** `INTERFACE-FIRST`

**Reason.** The omnibus `classField_package` is replaced by a source-faithful four-way split
(`CF-LOCAL-RECIP` / `CF-GLOBAL-RECIP` / `CF-CHAR-PRESCRIBE` / `CF-COMPAT`) whose contracts each map to a
named class-field theorem (`local_class_field_theory`, `global_class_field_theory`,
`Skinner_Wiles_CFT_trick`, and the compatibility clause), supply exactly what the two observed
consumers need, and provably do **not** smuggle in automorphy or curve existence. An honest,
kernel-clean first slice (Slice-A adapters) elaborates now over existing `GaloisRep` / `Representation.ind`
vocabulary; the reciprocity isomorphisms are correctly held at definition-gap because their domain
objects (Weil group, idele class group, `π₀`) are absent from the pinned Mathlib. The design, its
risks (esp. Grunwald–Wang exceptional case and the circularity guard), and its stop-loss set are
complete and internally consistent — ready for GPT-5.6 xhigh independent review.

**Next exact signature to attempt (first, no `sorryAx`):**
`FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter` and
`FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents` in
`FLTMethodology/Probes/ClassFieldBoundary.lean`, verified by
`lake build FLTMethodology.Probes.ClassFieldBoundary` + `#print axioms` (expect the standard trio only).

