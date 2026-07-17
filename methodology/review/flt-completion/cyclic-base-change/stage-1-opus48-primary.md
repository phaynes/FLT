# Opus 4.8 primary design output

Component: `cyclic-base-change / FLT-CBASE`
Agent: `opus48-primary-designer-d10`
Model/backend: `claude-opus-4-8` / `claude-code`
Verdict: **READY-FOR-GPT-REVIEW**
Bridge duration: 705919 ms
Claude session: `7bab9eb1-d242-4d1d-9bd6-674fddde1c13`

The model completed within its scheduled difficulty budget. Claude's plan-mode transport wrote the
full report to `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-jiggly-mccarthy.md` despite the read-only prompt and returned only a summary to the bridge.
That out-of-repository provider side effect is recorded honestly; the report below is the complete
plan artifact copied into the governed component directory. No external file was edited or deleted
by this orchestration step.

---

# Stage-1 Primary Design — `cyclic-base-change` / `FLT-CBASE`

**Actor:** Opus-first primary producer (first attempt). **Mode:** read-only design; no repo edits.
**Repository:** `/Volumes/second-store/devel/proof-forks/FLT`
**Frozen baseline:** branch `methodology/varro-proof-program-20260716`, SHA `827eb969…`.
**Baseline fidelity check:** `git diff 827eb969 HEAD -- FLT/GaloisRepresentation/Automorphic.lean`
is **empty**; baseline is an ancestor of current HEAD `66e4f1e`; the intervening commits touch only
methodology/routing. Every signature below is byte-faithful to the frozen theorem.

**Verdict (Opus ladder): `READY-FOR-GPT-REVIEW`** — carrying the nonfable §9 sub-verdict
**`INTERFACE-FIRST`**. Reason in §9.

---

## Context (why this exists)

The repo exports an **admitted** theorem `cyclic_base_change` (`FLT/GaloisRepresentation/Automorphic.lean:137`,
body `sorry` at `:194`; axiom closure `[propext, sorryAx, Classical.choice, Quot.sound]`). It is the
sole `sorryAx`-only (non-`knownin1980s`) leak in the clean import surface, formally pinned by
`methodology/evidence/contracts/ExistingAdaptersAudit.lean:116`. The graph plans two downstream
consumers (FLT-MLT, FLT-BRAUER-FAMILY) that need **more than** the current statement provides. This
design freezes source-faithful signatures, separates forward transfer from descent/image, and states
a bounded interface-first build with explicit stop-loss gates. **It does not attempt T3 closure**: the
analytic transfer/descent content is unformalized and has no source-of-record in the tree.

---

## 1. Observed baseline and exact consumers

**Current theorem type (reproduced faithfully; `Automorphic.lean:137–194`).** Over `F` totally real
number field with `hF : Even (Module.finrank ℚ F)`, and `E/F` with
`[IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]`, prime `p` with cyclotomic-finrank conditions `hp`/`hpE`,
`V` a rank-2 `ℚ_[p]ᵃˡᵍ`-module, `ρ : GaloisRep F ℚ_[p]ᵃˡᵍ V`, and hypotheses
`hρirred` (irreducibility of `ρ.map (algebraMap F E)`), `hρdet` (det = cyclotomic character),
`hρflat` (∃ finite-free-over-`ℤ_[p]` integral model `ρ₀` flat above `p`), `hS`/`hρunram`
(unramified outside `p·S`), `hρtame` (rank-one tame quotient at each `v ∈ S`):
```
(ρ.IsAutomorphicOfLevel p hp hV S) ↔
  ((ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
     (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S))
```

**Cyclic vs solvable vs iteration.** Named "Cyclic base change" but stated for **finite solvable**
`E/F` (`[IsSolvable (E ≃ₐ[F] E)]`, `:143`). Mathematically this is the **solvable-iteration**
theorem, obtained classically by iterating prime-degree cyclic steps. The name is a misnomer; the
scope is solvable. This matters for the component split (§3) and for the iteration counterexamples (§6).

**Actual consumers.** Exhaustive grep of `FLT/` for `cyclic_base_change` / `IsAutomorphicOfLevel`
returns **no real Lean application anywhere**. Every reference is one of:
- `#check` / `#print axioms` **methodology probes**: `FLTMethodology/Probes/ExistingContracts.lean:27`,
  `…/LibraryMatches.lean:30`, `…/MLTSourceBoundary.lean:123,130`.
- **Contract/quarantine audits** (type + axiom pin, not applied):
  `methodology/evidence/contracts/ExistingAdaptersAudit.lean:17,66,116`; doc-note in
  `FLT/Components/Existing.lean:22`.
- `IsAutomorphicOfLevel` is used in Lean **only** as both sides of `cyclic_base_change`'s own conclusion.

**Graph-only planned consumers** (all `current_state: absent`, no Lean code):
| Consumer (graph id) | Edge | Exact conclusion it needs from base change |
|---|---|---|
| **FLT-MLT** `modularity_lifting_weight_two_of_taylor2018` | `E-CBASE-MLT` (`proof-graph.ndjson:81`) | Forward transfer **and** the exact **descent/image** theorem; final target is the repository `IsAutomorphicOfLevel` at proved level `S`. |
| **FLT-BRAUER-FAMILY** `CompatibleFamily.of_potentially_automorphic` | `E-CBASE-BRAUER-FAMILY` (`:103`) | Forward base change **and** descent (solvable base changes + descent) **plus coefficient/semisimplification transport** (`source_condition_risks`, `proof-obligations.ndjson:24`). |

FLT-CBASE's own `source_condition_risks` (`proof-obligations.ndjson:13`):
*"The Skinner–Wiles reduction also needs characterization of the image and multiplicity one, not only
forward base change."* Its `completion_gate`: *"Forward transfer and the exact descent/image theorem
required by MLT have acceptable target-stage axiom closure."* Related absent nodes: **FLT-JL** carries
multiplicity-one + local/level compatibility (`:18`); **FLT-MLT-SOURCE** warns the source conclusion is
*level-free GL2 automorphy and must not be replaced by `IsAutomorphicOfLevel S`* (`:14`).

**Takeaway:** the current iff already fuses forward + descent, but downstream needs image
characterization, multiplicity one, and (for BRAUER) coefficient transport — none of which the
statement supplies. There is no live Lean dependency to break, so the public statement can be safely
narrowed/split.

---

## 2. Source theorem boundary

**No primary base-change source of record exists in the tree.** `SOURCE-REGISTER.md` has **no** row
for cyclic/solvable/Langlands base change, Arthur–Clozel, or Jacquet–Langlands. The closest is
**SRC-004** (`SOURCE-REGISTER.md:12`): FLT blueprint `blueprint/src/chapter/ch04overview.tex`,
*"Potential modularity and modularity-lifting sketch,"* status **"Read; explicitly incomplete
upstream."** The mathematical *need* is stated only as blueprint prose:
- `ch04overview.tex:86–88`: Skinner–Wiles reduction *"needs cyclic base change for GL(2) and also a
  characterisation of the image of the base change construction; this seems to need a multiplicity one
  result, which … will need Jacquet–Langlands as well."*
- `chtopbestiary.tex:212–214`: needs *"cyclic base change plus classification of image, all for
  totally definite quaternion algebras … There seems to be little point formalising the statements of
  the theorems if we cannot yet even formalise the definition of an automorphic representation
  properly."*
- `FLT/Assumptions/README.md:52–57`: lists *"Cyclic base change for GL_2 and classification of image"*
  and notes classification-of-image *"might well also need multiplicity 1 for GL_2, … a separate project."*

**Marked unavailable/unverified:**
- **Langlands, cyclic base change for GL(2)** — cited **by name only** in `FLT/Assumptions/KnownIn1980s.lean`
  and `blog.md:39` (author: *"only the most superficial understanding of"*). No title, DOI, page, or file.
- **Arthur–Clozel, *Simple Algebras and Base Change*** — **zero occurrences** anywhere in the tree.
  Any design citing it or a Langlands theorem number cites from memory, **not** from repo material.
- **Jacquet–Langlands** — named as an **open obligation / missing interface** (`SOURCE-REGISTER.md:47`,
  `LIBRARY-SURVEY.md:31`); no source theorem or locator.
- Sibling Stage-1 outputs `stage-1-gpt56xhigh.md` and `stage-1-sonnet5.md` are **both CANCELLED, no
  verdict, no signatures, no sources** (600 s timeouts). No prior design content to inherit.

**Classical-GL2 ↔ repository-predicate mismatch.** Classical base change concerns automorphic
representations of `GL₂(𝔸_F)`. The repository `IsAutomorphicOfLevel` (§4) is a **far more specific
quaternionic** predicate: a *totally definite quaternion algebra `D/F` of discriminant 1*
(unramified everywhere), *weight 2*, *level `U₁(S)`*, packaged as a `ℤ_[p]`-algebra map from a
**concrete Hecke algebra** to `A`, with the eigensystem pinned by
`trace ρ(Frobᵥ) = π(Tᵥ)` and `det ρ(Frobᵥ) = N(v)` at good `v`. To land this predicate one needs, on
top of GL2 base change: (i) **Jacquet–Langlands** to move GL2 ↔ the quaternion algebra; (ii)
**multiplicity one** to pin a single eigensystem; (iii) **image characterization** ("descends up to
twist") to run the descent direction; (iv) **level/conductor matching** `U₁(S) ↔ U₁(S_E)`. The
current admitted iff silently compresses (i)–(iv) into `hρtame` + the biconditional. This mismatch is
the core reason the theorem must remain a **named T2 boundary**, not a fake T3 proof.

---

## 3. Minimal component split (reject the monolith)

The current single iff is a **monolith whose hypotheses (`hρtame`, `hρflat`) plus the biconditional
encode the hard conclusion** (image characterization + descent). Split by observed-consumer need:

- **C1 — Forward transfer** (needed by MLT + BRAUER): `ρ` automorphic over `F` ⟹ `ρ.map` automorphic
  over `E` at the pulled-back level. This is the tractable direction (restrict the eigenform along
  `E/F`, transport the Hecke system).
- **C2 — Descent / image characterization** (needed by MLT + BRAUER): `ρ.map` automorphic over `E`
  ⟹ `ρ` automorphic over `F`, **given** `ρ|G_E` irreducible (not induced). This is the hard direction;
  it consumes C3, C4, C5.
- **C3 — Character twists** (needed by C2's image characterization): the "descends up to twist"
  vocabulary. **No twist operator exists** on `GaloisRep` or automorphic forms (§5). New.
- **C4 — Strong multiplicity one** (needed by C2, carried by FLT-JL): pins the eigensystem so descent
  targets a unique form. Absent; belongs to FLT-JL, not CBASE.
- **C5 — Local / conductor compatibility** (needed by C1 and C2): well-definedness and correctness of
  `S ↦ preimageComapFinset … S = S_E`; transport of unramified/tame-rank-one data across places of `E`
  above `S`; det = cyclotomic under restriction.
- **C6 — Coefficient transport** (needed by **BRAUER only**, not by the CBASE iff): align coefficient
  fields / semisimplification with the family type. Keep **out** of the CBASE public statement; expose
  as a separate BRAUER-owned obligation.

**Rejected:** a single `cyclic_base_change` iff that keeps `hρtame`/`hρflat` bundled — it hides C2–C5
inside hypotheses and the biconditional, so a "proof" would be an axiom in disguise.

---

## 4. Exact Lean signatures in dependency order

Namespace `GaloisRep`; universe `u` (number field / quaternion algebra) as in the file. Labels:
`EXISTING-PROVED`, `EXISTING-ADMITTED`, `PROPOSED`.

**D0. `GaloisRep.IsAutomorphicOfLevel` — EXISTING-PROVED** (`def`, axiom-clean; `Automorphic.lean:70`).
Retain unchanged. Signature (faithful):
```lean
def GaloisRep.IsAutomorphicOfLevel
  {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
  (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
  {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A] [ContinuousSMul ℤ_[p] A]
  {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    (_hV : Module.finrank A V = 2)
  (ρ : GaloisRep F A V) (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop
```

**Supporting proved-defs (all EXISTING-PROVED, no `sorry`)** to build on:
`GaloisRep.map` / `.baseChange` / `.conj` / `.det` / `.toLocal` / `.IsUnramifiedAt` / `.IsFlatAt` /
`.IsIrreducible` / `.ker` (`FLT/Deformations/RepresentationTheory/GaloisRep.lean`);
`HeightOneSpectrum.preimageComapFinset` (`FLT/DedekindDomain/IntegralClosure.lean:164`);
`localTameAbelianInertiaGroup`, `adicArithFrob` (`…/AbsoluteGaloisGroup.lean:178,213`);
`HeckeAlgebra`, `HeckeAlgebra.T`, `U₁Data` (`…/HeckeOperators/Concrete.lean:874,911,374`);
`IsQuaternionAlgebra`, `WithRigidification`, `WeightTwoAutomorphicForm`.

**Structural lemmas (PROPOSED, genuinely provable now — the buildable core):**

**D1. Even degree of the top field** (makes the RHS non-vacuous; §6 risk):
```lean
theorem GaloisRep.even_finrank_of_even_base
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]
    (hF : Even (Module.finrank ℚ F)) : Even (Module.finrank ℚ E)
```
Proof sketch: `Module.finrank_mul_finrank ℚ F E` (verified present in Mathlib) ⟹
`finrank ℚ E = finrank ℚ F * finrank F E`, then `Even.mul_right`. **PROPOSED, provable, axiom-clean.**

**D2. Level pullback well-definedness / re-index** (C5, thin): faithful statements that
`preimageComapFinset (𝓞 F) F E (𝓞 E) S` is the level `S_E` and behaves under the good-place condition
`↑p ∉ v.asIdeal`. **PROPOSED**; mostly re-exports of the existing `preimageComapFinset` API.

**D3. Restriction-of-irreducibility interface** (C2 precondition): there is **no** lemma linking
`GaloisRep.map` to `IsIrreducible` (§5). `hρirred` is a raw hypothesis. Expose the intended shape:
```lean
-- INTERFACE (PROPOSED): no proof attempted here; consumer supplies the hypothesis.
def GaloisRep.RestrictsIrreducible
    {F E A V : Type*} [Field F] [Field E] [Algebra F E] /- … -/
    (ρ : GaloisRep F A V) : Prop := (ρ.map (algebraMap F E)).IsIrreducible
```

**Forward / descent boundaries (PROPOSED interface scaffolds — NOT proofs):**

**D4. Forward transfer (C1):**
```lean
-- INTERFACE SCAFFOLD (PROPOSED, boundary): analytic content unformalized.
theorem GaloisRep.isAutomorphic_map_of_isAutomorphic
    /- same context as cyclic_base_change -/ :
    ρ.IsAutomorphicOfLevel p hp hV S →
    (ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S)
```

**D5. Descent / image characterization (C2):**
```lean
-- INTERFACE SCAFFOLD (PROPOSED, boundary): needs C3 twists, C4 mult-one, FLT-JL.
theorem GaloisRep.isAutomorphic_of_isAutomorphic_map
    /- same context + hρirred + hρtame + hρflat -/ :
    (ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S) →
    ρ.IsAutomorphicOfLevel p hp hV S
```

**D6. Public theorem disposition — `cyclic_base_change` (EXISTING-ADMITTED).** **Narrow + split, do not
retain the monolith.** Recompose it as a thin corollary `⟨D4, D5⟩` so its downstream scope
(the exact iff at level `S ↔ S_E`) is preserved for FLT-MLT/BRAUER, while the `sorry` migrates into the
two honestly-labelled boundary lemmas D4/D5. Keep the public name/type stable for the graph.

---

## 5. Pinned-library matches

| Declaration | Location | Class |
|---|---|---|
| `GaloisRep.map`, `.baseChange`, `.conj`, `.det`, `.toLocal`, `.IsUnramifiedAt`, `.IsFlatAt`, `.IsIrreducible`, `.ker` | `…/GaloisRep.lean` | **exact** (proved defs/classes) |
| `IsAutomorphicOfLevel` | `Automorphic.lean:70` | **exact** proved `def` (predicate only) |
| `preimageComapFinset`, `localTameAbelianInertiaGroup`, `adicArithFrob`, `HeckeAlgebra(.T)`, `U₁Data`, `IsQuaternionAlgebra`, `WithRigidification`, `WeightTwoAutomorphicForm` | as in §4 | **exact** proved |
| `Module.finrank_mul_finrank` (for D1) | Mathlib `FieldTheory/*` | **exact** proved |
| `cyclotomicCharacter` | Mathlib `Cyclotomic/CyclotomicCharacter.lean:307` | **exact** proved |
| `cyclic_base_change` | `Automorphic.lean:137` | **signature-only / admission-dependent** — **NOT counted as a proved match** (`sorryAx`; matches `library-matches.ndjson:LIB-011` verdict `admission-dependent`) |
| `GaloisRep.map`→irreducibility transfer | — | **missing** (only unrelated `Representation.IsAbsolutelyIrreducible`, `…/Irreducible.lean:33`) |
| character twist on `GaloisRep` / forms | — | **missing** (no `twist` anywhere in Deformations/AutomorphicForm) |
| `IsAutomorphicOfLevel` restriction/pushforward along `algebraMap F E` | — | **missing** (only `cyclic_base_change` itself) |

---

## 6. Counterexamples and statement risks

1. **Cyclic vs solvable / iteration.** Statement uses `IsSolvable`, name says cyclic. Solvable proof
   iterates prime-degree cyclic steps; **each hypothesis must be preserved under one step and through
   iteration**: irreducibility after further restriction, det = cyclotomic, flat integral model, tame
   rank-one quotient, level pullback. Risk: a cyclic-only lemma cannot be re-exported as the solvable
   statement without an explicit induction over the derived series.
2. **Even-degree of `E` (missing side-condition → possible vacuous RHS).** The theorem has
   `hF : Even (finrank ℚ F)` but **no** `Even (finrank ℚ E)` hypothesis. A totally definite quaternion
   algebra of discriminant 1 over `E` exists only if `[E:ℚ]` is even; otherwise the RHS `∃ D …` is
   vacuously false and the iff would be false in the forward direction. Mitigated by **D1**
   (`Even (finrank ℚ E)` is derivable from `hF` via the tower) — but this must be **proved**, not
   assumed. Flag: confirm the iff is not vacuously satisfiable through an empty RHS.
3. **Irreducibility after restriction (endpoint orientation).** `hρirred` is on `ρ.map` (over `E`),
   which is *stronger* than irreducibility over `F` and is exactly what blocks `ρ` from being induced
   — the precondition for **descent (D5)**, not forward (D4). Placing it as a global hypothesis is
   fine, but a proof must use it only in D5; using it in D4 would signal a mis-split.
4. **False-iff-direction.** Forward (D4) is the tractable direction; descent (D5) is the hard one
   requiring image characterization + multiplicity one + JL. A "proof" of the iff that discharges D5
   cheaply is almost certainly hiding an axiom. **Never** let the `↔` be closed without both boundaries
   discharged or explicitly named.
5. **Pullback of level / ramification transport.** `S_E = preimageComapFinset … S`. Must verify
   good-place condition `↑p ∉ v` transports, and that `U₁(S)` at `v` matches `U₁(S_E)` at places of `E`
   above `v` (tame rank-one quotient `hρtame` transported to `E`). Risk: `preimageComapFinset` gives the
   set-theoretic pullback but the local level structure match is unproven.
6. **Coefficient / representation-space identification.** Within the iff both sides share the same `V`
   and `A = ℚ_[p]ᵃˡᵍ` (via `ρ.map`, same module) — so **no coefficient transport is needed inside CBASE**.
   BRAUER's coefficient/semisimplification transport (C6) is a *separate* obligation; do not smuggle it
   into the iff.
7. **Descent up to twist / invariant characters.** Image characterization is "descends up to twist,"
   but **no twist vocabulary exists**. Any descent statement must first introduce C3, else "image
   characterization" is unstatable and D5 cannot even be phrased faithfully.
8. **Multiplicity one.** Descent targets a *unique* eigensystem; without C4 (owned by FLT-JL) the
   descended form is not pinned. Risk of a well-typed-but-false D5.
9. **Circular dependence.** FLT-MLT depends on FLT-CBASE (`E-CBASE-MLT`); FLT-POTMOD depends on
   FLT-MLT. Therefore **CBASE must not be proved via potential automorphy or modularity lifting** —
   that is a cycle. Hard stop-loss gate (§8).
10. **Unformalized analytic input.** The transfer/descent is a deep analytic theorem with **no Mathlib
    path and no source-of-record** (§2); the blueprint itself says there is "little point formalising
    the statements … if we cannot yet … formalise the definition of an automorphic representation
    properly." It must remain a **named T2 boundary**.

---

## 7. Smallest buildable first slice

**Bounded module (new file):** `FLT/GaloisRepresentation/BaseChange/Structural.lean`, importing
`FLT.GaloisRepresentation.Automorphic`. Contents, in order:
1. **D1** `even_finrank_of_even_base` — the one **genuinely provable, axiom-clean** lemma
   (`Module.finrank_mul_finrank` + `Even.mul_right`). ~5 lines.
2. **D2** level-pullback re-export lemmas (thin, over existing `preimageComapFinset`).
3. **D3–D5** as **interface scaffolds explicitly labelled `-- INTERFACE SCAFFOLD (boundary): not a proof`**,
   bodies `sorry`. These are *statements to be reviewed*, not claims of proof.

**Targeted commands:**
```
lake build FLT.GaloisRepresentation.BaseChange.Structural
#print axioms GaloisRep.even_finrank_of_even_base    -- expect: [propext, Classical.choice, Quot.sound]
#print axioms GaloisRep.isAutomorphic_map_of_isAutomorphic   -- expect: sorryAx present (boundary)
```
`even_finrank_of_even_base` must come back **clean** (no `sorryAx`); the D4/D5 boundaries will show
`sorryAx` and that is the honest, expected state.

**First likely residual Lean goal:** in D4, after unfolding both `IsAutomorphicOfLevel`, constructing
the `E`-side data `(D_E, π_E)` and Hecke system from the `F`-side `(D, π)` — i.e. base-changing the
quaternion algebra `E ⊗[F] D` (the instance `IsQuaternionAlgebra E (E ⊗[F] D)` already exists,
`Automorphic.lean:99`) and transporting the Hecke eigensystem to level `S_E`. That eigenform-transport
step is the analytic content and remains the T2 boundary.

---

## 8. Dependency graph and gates

**Local DAG:**
```
IsAutomorphicOfLevel (D0, PROVED)
        │
  ┌─────┼──────────────┬────────────────────┐
  ▼     ▼              ▼                     ▼
 D1    D2 (level     D3 (irred-restrict   [C3 twist] [C4 mult-one/FLT-JL]
Even   pullback)      interface)               │            │
  │     │              │                        ▼            ▼
  └──►  D4 forward ◄────┘        D5 descent/image  ◄─────────┘
        (boundary)                (boundary)
              └───────────┬───────────┘
                          ▼
              cyclic_base_change = ⟨D4, D5⟩   (public iff, scope preserved)
                          │
              ┌───────────┴────────────┐
              ▼                         ▼
          FLT-MLT (absent)     FLT-BRAUER-FAMILY (absent, + C6 coefficient transport)
```

**Completion condition.** D1/D2 proved & axiom-clean; D4/D5 either (a) closed with a kernel-clean proof
+ declaration axiom audit for genuine **T3**, or (b) retained as **named T2 boundaries** with `sorryAx`
audited and sourced. `cyclic_base_change` recomposed as `⟨D4, D5⟩` with no scope loss.

**Stop-loss gates (halt and report `OBSTRUCTION`/boundary if any trips):**
- **G1 source mismatch:** no primary base-change source is in-tree (confirmed §2). Any T3 claim citing
  Langlands/Arthur–Clozel by number is citing from memory → reject.
- **G2 false-iff direction:** D5 (descent) closed without C3+C4 present → reject as hidden axiom.
- **G3 missing automorphic-rep vocabulary:** no twist operator, no GL2↔quaternion transfer at the
  representation level (that is FLT-JL, absent) → D5 cannot be *faithfully stated*, only scaffolded.
- **G4 unformalized analytic theorem:** transfer/descent stays a **named T2 boundary**, never a fake T3
  proof; do **not** introduce a generic "base-change authority" axiom.
- **G5 cycle:** any route proving CBASE via FLT-MLT/FLT-POTMOD/potential-automorphy → reject (§6.9).

---

## 9. Verdict

**`READY-FOR-GPT-REVIEW`** (nonfable §9 sub-verdict: **`INTERFACE-FIRST`**).

**Reason.** The baseline is fully and faithfully characterized; sources are honestly marked
unavailable (no base-change source-of-record; Arthur–Clozel absent; Langlands cited by name only); the
monolithic iff is split into forward (D4) and descent/image (D5) with twists/mult-one/coefficient
transport pushed to their correct owners (C3, FLT-JL, BRAUER); signatures are frozen source-faithfully;
counterexamples and the missing even-`E` side-condition are enumerated; and there is a bounded first
slice with a genuinely provable, axiom-clean lemma (D1) plus clearly-labelled boundary scaffolds. This
is complete and defensible enough for GPT review. It is **not** a T3 closure and does not pretend to be:
the transfer/descent is an unformalized analytic theorem with no source in the tree, so the correct
disposition is interface-first (named T2 boundary), not a proof.

**Next exact signature to attempt:** `GaloisRep.even_finrank_of_even_base` (D1) — the one clean,
provable lemma — in a new `FLT/GaloisRepresentation/BaseChange/Structural.lean`, then land D2 and stub
D4/D5 as reviewed boundary scaffolds.

