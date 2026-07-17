# Primary Opus 4.8 Stage-1 Design — `auxiliary-residual-image`

Component `auxiliary-residual-image` (owner FLT-413) → three critical-path obligations:
`FLT-AUX-LOCAL-FIELD` (`FLT.PotentialModularity.AuxiliaryFieldCondition`),
`FLT-AUX-CURVE` (`FLT.PotentialModularity.exists_auxiliary_curve`),
`FLT-RESIDUAL-IMAGE` (`FLT.ModularityLifting.cyclotomicRestrictionIrreducible`).

- Repo `/Volumes/second-store/devel/proof-forks/FLT`; pinned Mathlib `a3364faec42918fcd84a03a255b50570129f9ead`;
  toolchain `leanprover/lean4:v4.32.0-rc1`; build config `lakefile.toml`.
- Role: first-attempt Opus-first primary producer; read-only; no prior Stage-1 result exists for this
  component (`review/flt-completion/auxiliary-residual-image/` holds only the prompt).
- Design budget 3600 s; difficulty 10; **early interface work only — builds remain dependency-gated.**

---

## Context (why this design exists)

The blueprint's potential-modularity step (SRC-004, `ch04overview.tex` L93–98) needs, for a
hardly-ramified `ρ`, a totally real auxiliary field `F` and an elliptic curve `A/F` whose **mod-ℓ**
representation is `ρ|G_F` and whose **mod-p** representation is **induced from a character**; the
induced curve is modular by converse theorems + Jacquet–Langlands, and a modularity-lifting theorem
(Taylor 2018, SRC-016, Thm 2.1.1) then transfers modularity back to `ρ`. That lifting theorem carries
a **cyclotomic-restriction irreducibility** hypothesis ("absolutely irreducible when restricted to
`F(ζ_ℓ)`", L62–64) that must hold at **two** concrete applications (CM-induced seed at ℓ₁,
auxiliary-curve residual at ℓ₂). This component freezes the three separated contracts — **local field**,
**curve existence**, **residual-image adequacy** — that the assembly (`FLT-POTMOD`) and Taylor–Wiles
prime selection (`FLT-TW-PRIMES`) consume.

Two terminal risks govern the work and dictate the separation:
- **R2** (High/Terminal): *residual irreducibility mistaken for cyclotomic irreducibility or
  adequacy.* Control = the separate `FLT-RESIDUAL-IMAGE` node. → the curve interface must **not**
  assert irreducibility; it produces the representation as data.
- **R4** (Medium/Terminal): *split-completely silently weakened to unramified* (or vice-versa).
  Control = `FLT-AUX-LOCAL-FIELD`. Corrected route = **unramified, not split** (Taylor 2018, not
  Taylor 2006 / SRC-012); **no `SL₂(F_p)` image bridge** (Gee 2022 / SRC-013 rejected).

---

## 1. VERDICT — `UNCERTAIN`

Three source-faithful **interfaces** can be, and below are, frozen with clean two-layer separation,
exact consumer inventory, dependency order, hostile counterexamples, signature probes, and a genuinely
gate-independent first buildable slice. But promotion to `READY-FOR-GPT-REVIEW` is blocked by **four
named gates, all inherited and none resolvable by model effort at this node**:

- **G-MB — Moret–Bailly source + primitive gate (inherited).** `FLT-MORET-BAILLY` is itself
  `UNCERTAIN`/`reviewing`: primary 1989 text absent (SRC-011 "exact Lean statement absent"), and there
  is **no moduli-point / `T(L_v)`-topology primitive** in the pin. This gates `exists_auxiliary_curve`'s
  moduli-point existence and `AuxiliaryFieldCondition`'s local-open construction. The curve/field
  *interface* freezes; the *existence bridge* does not.
- **G-MLT — modularity-lifting-source definition gap (inherited).** `FLT-MLT-SOURCE` "cannot yet
  elaborate honestly" (MLT-SOURCE-CONTRACT.md): the residual/coefficient/semisimplification,
  crystalline, and Hodge–Tate vocabulary Taylor 2018 hyp. (2)(4)(6)(8) require is **absent**. This
  gates the *exact* residual representation and coefficient field that `cyclotomicRestrictionIrreducible`
  must be stated over, and the local conditions `AuxiliaryFieldCondition` must supply (hyp. 5, 7).
- **G-CF — class-field definition gap (inherited).** `FLT-CLASS-FIELD` is a definition gap; **all of
  class field theory is absent from the pin** (reciprocity, Artin map, Hecke/`ContinuousCharacter`,
  CM-induced Galois characters = NONE FOUND). This gates "mod-p induced from a character" in AUX-CURVE
  and the CM-induced seed at ℓ₁ in RESIDUAL-IMAGE.
- **G-IND — induced-irreducibility library gap (this node).** Mathlib has `Representation.ind` and
  Frobenius reciprocity as an adjunction, but **no Mackey / induced-character irreducibility
  criterion** (NONE FOUND). Proving the CM-induced seed irreducible over `F(ζ_ℓ)` — the
  "character-ratio" content of RESIDUAL-IMAGE — must be built. This is the one gate this node *could*
  start on (see §9 build units U3), but it is unbounded (`lean_risk: unbounded`).

Verdict is `UNCERTAIN`, not `OBSTRUCTION` (no redesign forced; the three-contract separation is
coherent and buildable in principle), and not `REVISE` (nothing produced is wrong). It matches the
upstream discipline: this component sits strictly downstream of `FLT-MORET-BAILLY` (UNCERTAIN),
`FLT-MLT-SOURCE` (definition-gap), and `FLT-CLASS-FIELD` (definition-gap), and inherits their gates.
`source-design.ndjson` records `dor: BLOCKED` — this design keeps it BLOCKED and names the four gates
that must close (G-MLT + G-MB for AUX-CURVE/AUX-LOCAL-FIELD; G-MLT + G-CF + G-IND for RESIDUAL-IMAGE)
before a review-ready freeze.

---

## 2. CURRENT EXACT BOUNDARY

- **All three target declarations are absent from Lean.** Grep over `FLT/` for
  `exists_auxiliary_curve`, `AuxiliaryFieldCondition`, `cyclotomicRestrictionIrreducible` returns
  **zero hits**; they exist only as `lean_declaration` strings in the planning NDJSON.
- **`FLT/PotentialModularity/` does not exist** — AUX-CURVE and AUX-LOCAL-FIELD modules
  (`FLT.PotentialModularity.AuxiliaryCurve`, `.AuxiliaryField`) are net-new.
- **`FLT/ModularityLifting/`** exists with exactly one file, `Conditions.lean`, holding only
  `BlueprintSGood` (a `Prop` structure of the four S-good conditions, no automorphy conclusion). The
  expected `FLT.ModularityLifting.ResidualImage` module is net-new.
- **States:** AUX-CURVE `current_state: absent`, review `unreviewed`; AUX-LOCAL-FIELD and
  RESIDUAL-IMAGE `current_state: definition-gap`, review `revision-required`; all three
  `kernel_probe_state: absent`. No `sorry`/`axiom` stubs to retire — the "stubs" live in the NDJSON.
- **Library-match verdicts:** MISS-012 (RESIDUAL-IMAGE) `blocked` — "No exact theorem establishes the
  source-selected cyclotomic irreducibility or adequacy condition"; MISS-014 (AUX-LOCAL-FIELD)
  `blocked` — "cannot be frozen until the lifting theorem selects split-completely or unramified."
- **Load-bearing existing FLT assets to build against** (all elaborate today):
  - `GaloisRep K A M` — `FLT/Deformations/RepresentationTheory/GaloisRep.lean:49` (coefficient-agnostic:
    mod-ℓ / mod-p / ℓ-adic by choice of `A`). Ops: `.map (f : K →+* L)` (:76, restriction to `G_L`),
    `.det` (:202), `.baseChange` (:210), `.toLocal v` (:309), `.toRepresentation` (:399).
  - `GaloisRep.IsIrreducible` — `GaloisRep.lean:404` = `ρ.toRepresentation.IsIrreducible`.
  - `GaloisRep.IsUnramifiedAt` (class, :316), `IsFlatAt` (:391).
  - `IsHardlyRamified` — `FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96` (4-field `Prop`
    structure; PROVED as a definition; the Frey curve *satisfies* it only via `sorry` in Frey.lean).
  - `GaloisRep.IsAutomorphicOfLevel` — `FLT/GaloisRepresentation/Automorphic.lean:70` (quaternionic,
    level-`S`; this is the **repository** predicate, distinct from Taylor's level-free conclusion).
  - `WeierstrassCurve.galoisRep (n) (hn)` — `FLT/EllipticCurve/Torsion.lean:487`:
    `GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)`. **This is the
    elliptic-curve mod-n Galois representation — present in FLT even though mathlib lacks it.** Key
    asset for AUX-CURVE. `nTorsion` at `FLT/EllipticCurve/TorsionDefs.lean:25`.
  - `FreyPackage` (`FLT/FreyCurve/FreyPackage.lean:75`), `freyCurve` (`Basic.lean:60`).
- **No `LinearDisjoint` use anywhere in `FLT/`** — disjointness will reuse mathlib
  `IntermediateField.LinearDisjoint` (`FieldTheory/LinearDisjoint.lean:157`).

---

## 3. SOURCE AND CONSUMER AUDIT — three separated contracts

### 3.0 Source clauses (locally verifiable)
- Blueprint SRC-004 `ch04overview.tex`: **L21–24** auxiliary field ("totally real … even degree,
  Galois over ℚ, unramified at ℓ, disjoint from K"); **L93–98** auxiliary curve (mod-ℓ `= ρ`, mod-p
  **induced from a character**); **L40–42/51–56** S-good; **L62–64** residual "absolutely irreducible
  when restricted to `F(ζ_ℓ)`". *The two-prime (ℓ₁/ℓ₂) split is a methodology-layer refinement
  (CONVERGENCE.md), **not** in the blueprint text.*
- Taylor 2018 SRC-016 Thm 2.1.1 (MLT-SOURCE-CONTRACT.md) 8 hypotheses; the ones this component
  supplies: **(4)** cyclotomic-restriction irreducibility → RESIDUAL-IMAGE; **(5)** ℓ unramified in F
  and **(7)** witness unramified at `v|ℓ` → AUX-LOCAL-FIELD (via good reduction at the chosen primes).
- Corrected route (CONVERGENCE.md L19–36): unramified-not-split; cyclotomic irreducibility proved
  **independently at both applications**; **no `SL₂(F_p)` image bridge**; conclusion is level-free GL2,
  kept separate from the quaternionic `IsAutomorphicOfLevel`.

### 3.1 Contract A — LOCAL FIELD (`FLT-AUX-LOCAL-FIELD`)
- **Produces:** a field-side predicate `AuxiliaryFieldCondition F …` bundling, as **separately named
  fields**: (source) both selected primes **unramified** in `F`; (Moret–Bailly clause i) `F` linearly
  disjoint from the **residual-kernel** avoidance extension and from the **cyclotomic** avoidance
  extension — **two** disjointness clauses; (project/Jacquet–Langlands, NOT source hyps) `IsTotallyReal
  F`, `Even (Module.finrank ℚ F)`, `IsGalois ℚ F`.
- **Design tension surfaced:** the obligation text also bundles "the auxiliary curve has **good
  reduction** above them" into this predicate, but the dependency edge is
  `E-AUX-LOCAL-FIELD-AUX-CURVE` (the curve is **downstream**). Good reduction is a **curve-relative**
  condition and therefore **cannot** live inside a field-only predicate without a forward reference.
  → **Decision:** keep `AuxiliaryFieldCondition` field-pure; expose good reduction as a clause of the
  AUX-CURVE existence conclusion (§3.2), parameterised by the produced curve. (Open question Q3.)
- **Consumes:** `FLT-MORET-BAILLY` (local opens + disjointness), `FLT-MLT-SOURCE` (which local shape —
  unramified — the lifting theorem demands: **R4**).

### 3.2 Contract B — CURVE EXISTENCE (`FLT-AUX-CURVE`)
- **Produces:** existence of `F` (with `AuxiliaryFieldCondition F`) and `A : WeierstrassCurve F`
  (`[A.IsElliptic]`) together with **data, not adequacy**:
  1. a mod-ℓ identification `A.galoisRep ℓ ≅ ρ|G_F` (first residual identification);
  2. the mod-p representation `A.galoisRep p` **is induced from a character** (an `IsInducedFromChar`
     predicate; second residual identification) — feeds converse theorems / JL;
  3. local conditions required by MLT: **good reduction of `A`** above the two selected primes
     (`WeierstrassCurve.HasGoodReduction`), parity, local flatness.
- **MUST NOT assert** that `A.galoisRep ℓ` or the induced mod-p rep is (cyclotomic-restriction)
  **irreducible / adequate** — that conclusion is RESIDUAL-IMAGE's, and the edge
  `E-AUX-CURVE-RESIDUAL-IMAGE` runs curve→residual-image. Baking it in reverses the edge (cycle) and
  fires **R2**. (Brief's explicit instruction.)
- **Consumes:** `FLT-MORET-BAILLY` (moduli point), `FLT-CLASS-FIELD` (character for the induced mod-p),
  `FLT-AUX-LOCAL-FIELD` (the field).

### 3.3 Contract C — RESIDUAL-IMAGE ADEQUACY (`FLT-RESIDUAL-IMAGE`)
- **Produces:** a **package of two independent theorems**, one per application:
  1. **ℓ₁, CM-induced seed:** the representation induced from the CM character, restricted to
     `F(ζ_{ℓ₁})`, is absolutely irreducible (built from induced-rep irreducibility + character-ratio
     avoidance — **G-IND / G-CF**);
  2. **ℓ₂, auxiliary-curve residual:** `A.galoisRep ℓ₂` restricted to `F(ζ_{ℓ₂})` is irreducible, using
     the Moret–Bailly **disjointness** data (`FLT-AUX-CURVE`) to preserve the concrete image.
- **Named distinct predicate:** `IsCyclotomicRestrictionIrreducible ρ ℓ :=
  GaloisRep.IsIrreducible (ρ.map (algebraMap F (F(ζ_ℓ))))` — this *names* the R2 distinction so plain
  `IsIrreducible` can never be silently substituted for it.
- **Consumes:** `FLT-HR-DEF` (the residual predicate feeding hyp. context), `FLT-MLT-SOURCE` (the exact
  residual coefficient field / semisimplified reduction the irreducibility is stated over — **G-MLT**),
  `FLT-AUX-CURVE` (the concrete ℓ₂ residual rep + disjointness).
- **Downstream:** `FLT-POTMOD` (Taylor hyp. 4) and `FLT-TW-PRIMES` (whose *adequacy/large-image*
  conditions are a **separate, stronger** notion — do not conflate irreducibility with adequacy here).

---

## 4. DEPENDENCY GRAPH (transitively reduced)

```
 Mathlib FOUND        FLT FOUND
 ─ IntermediateField  ─ GaloisRep(.map/.det/.toLocal/.IsIrreducible/.IsUnramifiedAt/.IsFlatAt)
   .LinearDisjoint    ─ WeierstrassCurve.galoisRep, nTorsion   ─ IsHardlyRamified
 ─ IsTotallyReal      ─ IsAutomorphicOfLevel (repo, level-S)   ─ BlueprintSGood
 ─ IsGalois, finrank  ─ FreyPackage / freyCurve
 ─ Representation.ind + indResAdjunction (Frobenius recip.)
 ─ IsIrreducible + IntertwiningMap (Schur)
 ─ CyclotomicField, cyclotomicCharacter, IsCyclotomicExtension
 ─ InfinitePlace.IsUnramified, IsNonarchimedeanLocalField, HasGoodReduction
        │
   ┌────┴─────────────────────────────────────────────┐
   ▼                                                   ▼
 [G-MB] FLT-MORET-BAILLY (UNCERTAIN)      [G-MLT] FLT-MLT-SOURCE (def-gap)   [G-CF] FLT-CLASS-FIELD
   moret_bailly_point                       residual/coeff/HT vocabulary       CM-induced characters
   │            │                                │              │                   │
   ▼            ▼                                ▼              │                   ▼
 A1 linearDisjoint_of_compositum   ┌──► FLT-AUX-LOCAL-FIELD ◄──┘        (character for induced mod-p)
   (pure field theory, FOUND)      │    AuxiliaryFieldCondition                     │
   │                               │    (unram + 2×disjoint + project)              │
   └───────────────┬───────────────┘              │                                │
                   ▼                               ▼                                ▼
             FLT-AUX-CURVE  ◄──────────────────────┴────────────────────────────────┘
             exists_auxiliary_curve
             (F + A; mod-ℓ = ρ; mod-p induced; good reduction)  — NO irreducibility here
                   │
                   ├───────────────► [G-IND] induced-irreducibility criterion (build here)
                   ▼
             FLT-RESIDUAL-IMAGE
             cyclotomicRestrictionIrreducible  (ℓ₁ CM-seed ∥ ℓ₂ aux-curve)
             = IsCyclotomicRestrictionIrreducible at two primes
                   │                   │
                   ▼                   ▼
             FLT-POTMOD           FLT-TW-PRIMES  (adequacy ≠ irreducibility — separate)
```

**Internal build order:** `AUX-LOCAL-FIELD → AUX-CURVE → RESIDUAL-IMAGE`.
**Gate map:** G-MB gates AUX-CURVE existence + AUX-LOCAL-FIELD opens; G-MLT gates the exact residual
statement in RESIDUAL-IMAGE + local shape in AUX-LOCAL-FIELD; G-CF gates the induced-character input;
G-IND gates the CM-seed irreducibility proof. The **definitions/predicates** (§5) elaborate ahead of
the gates; the **existence/irreducibility theorems** do not.

---

## 5. PROPOSED LEAN SIGNATURES (dependency order)

Two layers per contract: **(a)** predicates/definitions that elaborate against FOUND primitives today;
**(b)** existence/irreducibility theorems whose gated pieces are marked `⚠G-*` and left as
`/- … -/` placeholders (identified, not hidden), exactly as the moret-bailly precedent did.

### Layer A0 — pure field-theory adapter (FOUND; first slice candidate, shared with moret-bailly)
```lean
-- Split joint disjointness (from a single Moret–Bailly K^avoid = K_res ⊔ K_cyc) into the two factors.
theorem linearDisjoint_of_compositum
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L K₁ K₂ : IntermediateField K Ω)
    (h : L.LinearDisjoint (K₁ ⊔ K₂)) : L.LinearDisjoint K₁ ∧ L.LinearDisjoint K₂
```

### Layer A1 — RESIDUAL-IMAGE named predicate (FOUND; the R2-retiring definition — first slice, §9 U0)
```lean
namespace FLT.ModularityLifting
open NumberField
/-- Cyclotomic-restriction irreducibility: `ρ` restricted to the absolute Galois group of `F(ζ_ℓ)`
is irreducible.  NAMED distinctly from `GaloisRep.IsIrreducible` so plain residual irreducibility can
never be silently substituted (Risk R2).  `ρ.map (algebraMap F (CyclotomicField ℓ F))` is the
restriction to `G_{F(ζ_ℓ)}` (`GaloisRep.map`, GaloisRep.lean:76). -/
def IsCyclotomicRestrictionIrreducible
    {F : Type*} [Field F] [NumberField F]
    {k : Type*} [Field k] [TopologicalSpace k]          -- FIELD coeff: required by GaloisRep.IsIrreducible
    {V : Type*} [AddCommGroup V] [Module k V]
    {L : Type*} [Field L] [Algebra F L]                 -- L = the cyclotomic extension F(ζ_ℓ)
    (hL : /- L is (an) F(ζ_ℓ): IsCyclotomicExtension {ℓ} F L -/ True)
    (ρ : GaloisRep F k V) : Prop :=
  GaloisRep.IsIrreducible (ρ.map (algebraMap F L))
end FLT.ModularityLifting
```
*Fidelity notes.* (a) `GaloisRep.IsIrreducible` (`GaloisRep.lean:404`) requires the coefficient to be a
**field** `k` with `[Module k V]` — hence `k`, not a general `CommRing A`; for the residual/mod-ℓ rep
`k` is a finite field. (b) The cyclotomic extension is taken as an **abstract** `L/F` with an
`IsCyclotomicExtension {ℓ} F L` witness rather than the concrete `CyclotomicField ℓ F` term, to avoid
the mathlib `CyclotomicField`/`ℕ+`-argument and field-instance friction — this is the honest "elaborates
today" spelling. (c) For an ℓ-adic `ρ` the irreducibility is of its **residual reduction** (the G-MLT
semisimplified-reduction object), so the predicate is applied at the residual coefficient `k`, pinned by
G-MLT — never to a raw ℓ-adic integral rep.

### Layer A2 — AUX-LOCAL-FIELD predicate (FOUND field primitives; local shape gated by R4/G-MLT)
```lean
namespace FLT.PotentialModularity
open NumberField IsDedekindDomain
/-- Field-pure auxiliary-field conditions.  Local shape is **unramified** (R4: NOT split-completely);
disjointness is against the two avoidance extensions separately; project conditions are exposed as
separate fields and are NOT source hypotheses.  Good reduction is curve-relative → lives in AUX-CURVE. -/
structure AuxiliaryFieldCondition
    (F : Type*) [Field F] [NumberField F]
    (v₁ v₂ : HeightOneSpectrum (𝓞 F))                 -- the two selected finite places
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    (Kres Kcyc : IntermediateField F Ω) : Prop where   -- residual-kernel + cyclotomic avoidance exts
  unramified₁   : /- ⚠G-MLT: F/ℚ unramified at v₁ (Algebra.FormallyUnramified / place ramification) -/ Prop
  unramified₂   : /- ⚠G-MLT: unramified at v₂ -/ Prop
  disjoint_res  : (⊥ : IntermediateField F Ω).LinearDisjoint Kres  -- schematic; F↔Kres disjointness
  disjoint_cyc  : (⊥ : IntermediateField F Ω).LinearDisjoint Kcyc
  totallyReal   : IsTotallyReal F                    -- project (prescribe L_v = ℝ at ∞ places)
  evenDegree    : Even (Module.finrank ℚ F)          -- project / Jacquet–Langlands
  isGalois      : IsGalois ℚ F                        -- project / Jacquet–Langlands
/-- Existence bridge — ⚠G-MB (moret_bailly_point) + ⚠G-MLT (which local shape). -/
theorem exists_auxiliaryField
    {F₀ : Type*} [Field F₀] [NumberField F₀]
    (ρ : /- residual data pinned by G-MLT -/ True) :
    ∃ (F : Type*) (_ : Field F) (_ : NumberField F) (_ : Algebra F₀ F) …,
      /- AuxiliaryFieldCondition F … -/ True := by
  sorry -- gated: consumes moret_bailly_point (absent) + MLT-SOURCE local shape (def-gap)
end FLT.PotentialModularity
```

### Layer B — AUX-CURVE existence (⚠G-MB, ⚠G-CF; produces data, NOT irreducibility)
```lean
namespace FLT.PotentialModularity
open NumberField
/-- `A.galoisRep p` is induced from a (CM) character.  ⚠G-CF/G-IND: built from `Representation.ind`;
the character itself comes from FLT-CLASS-FIELD. -/
def IsInducedFromChar {F A V} … (ρ : GaloisRep F A V) : Prop :=
  /- ∃ CM subfield E and character χ : G_E → Aˣ with ρ ≅ Ind_{G_E}^{G_F} χ  (Representation.ind) -/ True
/-- Existence of the auxiliary curve.  Conclusion is **data**: mod-ℓ match, mod-p induced, good
reduction.  It deliberately contains **no** irreducibility/adequacy clause (Risk R2, brief). -/
theorem exists_auxiliary_curve
    {F₀ : Type*} [Field F₀] [NumberField F₀]
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime]
    {Vℓ : Type*} [AddCommGroup Vℓ] [Module (ZMod ℓ) Vℓ]
    (ρbar : GaloisRep F₀ (ZMod ℓ) Vℓ)
    (hHR : /- ρbar is (base-changed) hardly-ramified residual data -/ True) :
    ∃ (F : Type*) (_ : Field F) (_ : NumberField F) (_ : Algebra F₀ F)
      (_hAFC : /- AuxiliaryFieldCondition F … -/ True)
      (A : WeierstrassCurve F) (_ : A.IsElliptic) …,
        -- (1) mod-ℓ identification with ρ|G_F  (WeierstrassCurve.galoisRep, Torsion.lean:487)
        (Nonempty (A.galoisRep ℓ (by norm_num) ≃ₜ* /- ρbar.map (F₀→F) -/ sorry)) ∧
        -- (2) mod-p induced from a character
        (IsInducedFromChar (A.galoisRep p (by norm_num))) ∧
        -- (3) good reduction above the two selected primes  (mathlib HasGoodReduction)
        (∀ v ∈ /- {v₁,v₂} -/ (∅ : Set _), /- (A / F).HasGoodReduction at v -/ True) := by
  sorry -- gated: moret_bailly_point (G-MB) + classField_package (G-CF)
end FLT.PotentialModularity
```

### Layer C — RESIDUAL-IMAGE package (⚠G-MLT, ⚠G-CF, ⚠G-IND; the two-prime theorem)
```lean
namespace FLT.ModularityLifting
open NumberField FLT.PotentialModularity
/-- Cyclotomic-restriction irreducibility at BOTH Taylor applications.  Package of two independent
conclusions; neither is inherited from the other; no SL2 image bridge.  -/
theorem cyclotomicRestrictionIrreducible
    {F : Type*} [Field F] [NumberField F]
    (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    -- ℓ₁ CM-induced seed:
    {V₁} [AddCommGroup V₁] [Module (/- residual coeff, G-MLT -/ ZMod ℓ₁) V₁]
    (seed : GaloisRep F (ZMod ℓ₁) V₁) (hseed : IsInducedFromChar seed)
    (havoid₁ : /- ⚠G-CF character-ratio avoidance data at ℓ₁ -/ True)
    -- ℓ₂ auxiliary-curve residual (A from exists_auxiliary_curve):
    (A : WeierstrassCurve F) [A.IsElliptic]
    (hdisj₂ : /- ⚠ Moret–Bailly disjointness data preserving the ℓ₂ image -/ True) :
    IsCyclotomicRestrictionIrreducible seed ℓ₁ ∧
    IsCyclotomicRestrictionIrreducible (A.galoisRep ℓ₂ (by norm_num)) ℓ₂ := by
  sorry -- gated: induced-irreducibility criterion (G-IND) + residual coeff (G-MLT) + character (G-CF)
end FLT.ModularityLifting
```

*Binding notes:* `F`, the extension `A`, the two primes, the seed/aux representations, and the two
disjointness data are all bound. The `True`/`sorry`/`/- … -/` terms are exactly the gated pieces
(residual coefficient field = G-MLT; CM character/avoidance = G-CF; induced-irreducibility criterion =
G-IND; moduli point/good-reduction predicate = G-MB) — **named, not hidden**, and become concrete when
those upstream nodes resolve.

---

## 6. LIBRARY MATCHES (pinned `a3364fa…`)

| Proposed node | Pinned/FLT declaration | Verdict |
|---|---|---|
| coefficient-agnostic Galois rep | `GaloisRep K A M` — `FLT/…/GaloisRep.lean:49` | **FOUND (FLT)** |
| restriction to `G_{F(ζ_ℓ)}` | `GaloisRep.map (f : K →+* L)` — `GaloisRep.lean:76` | **FOUND (FLT)** |
| residual irreducibility | `GaloisRep.IsIrreducible` — `GaloisRep.lean:404` (`= toRepresentation.IsIrreducible`) | **FOUND (FLT)** |
| elliptic-curve mod-n rep | `WeierstrassCurve.galoisRep` — `FLT/EllipticCurve/Torsion.lean:487`; `nTorsion` `TorsionDefs.lean:25` | **FOUND (FLT; mathlib lacks it)** |
| Weierstrass / elliptic | `WeierstrassCurve` `Weierstrass.lean:77`, `IsElliptic` `:363` | FOUND (mathlib) |
| good reduction | `WeierstrassCurve.HasGoodReduction` — `EllipticCurve/Reduction.lean:281` | FOUND (mathlib) |
| induced representation | `Representation.ind` — `RepresentationTheory/Induced.lean:79`; adjunction `indResAdjunction :157` | FOUND (mathlib) |
| Schur / intertwiners | `Representation.IsIrreducible` `Irreducible.lean:30`; `IntertwiningMap` `Intertwining.lean:125` | FOUND (mathlib) |
| **induced-irreducibility (Mackey / char-ratio)** | — | **NONE FOUND (G-IND)** |
| cyclotomic field / character | `CyclotomicField` `Cyclotomic/Basic.lean:655`; `cyclotomicCharacter` `CyclotomicCharacter.lean:307`; `IsCyclotomicExtension` `:76` | FOUND (mathlib) |
| linear disjointness | `IntermediateField.LinearDisjoint` — `FieldTheory/LinearDisjoint.lean:157` | FOUND (mathlib; unused in FLT) |
| totally real / even deg / Galois | `IsTotallyReal` `TotallyRealComplex.lean:47`; `Even (finrank ℚ F)`; `IsGalois` `Galois/Basic.lean:58` | FOUND (mathlib) |
| unramified place | `InfinitePlace.IsUnramified` `…/Ramification.lean:184`; `Algebra.FormallyUnramified` `Unramified/Basic.lean:58`; `IsUnramifiedIn` `Locus.lean:98` | FOUND (mathlib) |
| nonarch. local field | `IsNonarchimedeanLocalField` — `NumberTheory/LocalField/Basic.lean:45` | FOUND (no `IsLocalField`) |
| finite places | `IsDedekindDomain.HeightOneSpectrum` — `…/Ideal/Lemmas.lean:495` | FOUND (mathlib) |
| CM totally-real subfield | `NumberField.CMField` (`complexConj`, `K⁺`) — `NumberField/CMField.lean:143,480` | FOUND (mathlib) |
| **class field theory** (reciprocity, Artin, Hecke char, CM-induced char) | — | **NONE FOUND (G-CF)** |
| **PGL2/SL2 finite-subgroup (Dickson), "adequate"/"big-image"** | — | **NONE FOUND — but NOT needed (no SL2 bridge; R2 uses irreducibility, TW-PRIMES owns adequacy)** |
| **moduli variety + `T(L_v)` topology / rational point** | — | **NONE FOUND (G-MB, inherited)** |
| Taylor 2018 residual/coeff/crystalline/HT vocabulary | — | **NONE FOUND (G-MLT, inherited; MLT-SOURCE-CONTRACT.md)** |

AINTLIB scan: `HasseWeil` (formal groups / point counting), `LeanModularForms` (Hecke, strong mult.
one), `Chebotarev` (Frobenius/unramified, abelian), `ModularCurves`, `NagellLutz` — **none** supply
torsion Galois representations, induced-rep irreducibility, or class field theory. No reuse for the
hard content.

---

## 7. COUNTEREXAMPLES AND FAILURE MODES (hostile checks)

1. **Residual irreducibility ≠ cyclotomic-restriction irreducibility (R2, terminal).** A rep can be
   irreducible over `F` yet **reducible** over `F(ζ_ℓ)` (e.g. an induced/dihedral rep whose inducing
   character becomes visible after the cyclotomic base change). Stating the conclusion as plain
   `GaloisRep.IsIrreducible` over `F` is the exact R2 error. Guard: the **named** predicate
   `IsCyclotomicRestrictionIrreducible` (restriction to `F(ζ_ℓ)`) — §5 A1.
2. **Irreducibility ≠ adequacy / big image.** `FLT-TW-PRIMES` needs *adequacy* (large-image, dual-Selmer
   killing) — strictly stronger than cyclotomic-restriction irreducibility. Do **not** let
   RESIDUAL-IMAGE's conclusion masquerade as adequacy (MISS-012). The corrected route uses **no**
   `SL₂(F_p)` image bridge (Gee 5.2 rejected); importing one would be scope creep and an unproved
   strengthening.
3. **Assuming the residual-image conclusion inside curve existence (brief; cycle).** `exists_auxiliary_curve`
   must produce `A.galoisRep ℓ`/mod-p as **data**, never asserting their irreducibility. The edge is
   curve→residual-image; asserting it reverses the edge (SCC cycle) and pre-supposes the theorem to be
   proved. §3.2/§5 Layer B carry no irreducibility clause.
4. **Split-completely silently substituted for unramified (R4, terminal).** Taylor 2018 needs ℓ
   **unramified** in `F`; Taylor 2006 (SRC-012) needs complete splitting. Fixing `L_v = K_v` (split) in
   `AuxiliaryFieldCondition` over-constrains and mis-serves the selected source. Keep the local shape
   **unramified**; never `IsSplit`.
5. **Two Moret–Bailly runs instead of one compositum.** Disjointness from `K_res` *and* `K_cyc` needs a
   **single** field `F` disjoint from `K_res ⊔ K_cyc`; running MB twice yields two different fields.
   Guard: `K^avoid = K_res ⊔ K_cyc`, then split via `linearDisjoint_of_compositum` (A0). Two separate
   disjointness fields in the predicate would be unsatisfiable jointly.
6. **Good reduction placed in the field-only predicate (forward reference).** Good reduction is a
   property of `A/F`, and `A` is downstream of the field. Putting it in `AuxiliaryFieldCondition` forces
   a forward reference to the curve → ill-formed dependency. Guard: good reduction is a clause of the
   AUX-CURVE conclusion (§3.1 decision, Q3).
7. **Coefficient-field confusion in the residual statement (G-MLT).** "The residual representation" is
   the semisimplified reduction of a stable lattice at a **specific** coefficient field; `A.galoisRep ℓ`
   (over `ZMod ℓ`) and an abstract ℓ-adic reduction are **not** definitionally the same object.
   RESIDUAL-IMAGE must be stated at the coefficient pinned by MLT-SOURCE, not a generic `ZMod`.
8. **Induced ≠ automatically irreducible.** `Representation.ind` of a character need **not** be
   irreducible; irreducibility depends on the inducing character not being fixed by the relevant Galois
   action (character-ratio non-triviality). There is **no** library lemma (G-IND); assuming
   "induced ⇒ irreducible" is false. The CM-seed proof is real mathematical content.
9. **Two applications collapsed into one.** The package must prove irreducibility **independently** at
   ℓ₁ (CM-seed) and ℓ₂ (aux-curve residual) — different reps, different cyclotomic fields
   (CONVERGENCE.md L31). A single lemma covering "both" by symmetry is unjustified; the ℓ₂ case uses
   MB disjointness, the ℓ₁ case uses character avoidance.
10. **Level-free vs quaternionic conclusion leak.** Taylor's conclusion is level-free GL2; the repo's
    `IsAutomorphicOfLevel S` is a separate derived boundary. RESIDUAL-IMAGE/AUX-CURVE must not smuggle
    the quaternionic predicate in as if it were the source conclusion (R3).

---

## 8. SIGNATURE PROBES (mirror `MazurNamedInterfaceProbe` / `QuaternionStabilizerSignatureProbe`)

Discipline: a single Lean file importing the relevant FLT module; the proposed signature with the hard
mathematical content passed **as a hypothesis** (never an axiom); discharged by `exact`; then
`#print axioms`. Three probes proposed (files under `methodology/evidence/probes/`):

- **P-RESID** `CyclotomicRestrictionProbe.lean` — checks `IsCyclotomicRestrictionIrreducible` elaborates
  and that `cyclotomicRestrictionIrreducible`'s conclusion type is exactly what a Taylor-2018 hyp-4
  consumer would read; injects the two irreducibility facts as hypotheses `(h₁ h₂ : …)` and returns the
  conjunction by `exact ⟨h₁, h₂⟩`; ends `#print axioms`. Elaboratable **today** for A1
  (`IsCyclotomicRestrictionIrreducible` def) since it uses only FOUND `GaloisRep.map`/`.IsIrreducible`
  + `CyclotomicField`; the full theorem probe stays gated on the G-MLT coefficient.
- **P-AFC** `AuxiliaryFieldConditionProbe.lean` — checks `AuxiliaryFieldCondition` elaborates with the
  `unramified`/project fields, injecting the Moret–Bailly disjointness + unramified facts as
  hypotheses; verifies the two-disjointness split via `linearDisjoint_of_compositum`. The project
  fields (`IsTotallyReal`, `Even`, `IsGalois`) are FOUND; the `unramified₁/₂` fields stay `⚠G-MLT`.
- **P-CURVE** `AuxiliaryCurveDataProbe.lean` — checks the AUX-CURVE conclusion **carries no
  irreducibility clause** and that `A.galoisRep ℓ` / `IsInducedFromChar` type-align with consumers;
  injects the existence witness as a hypothesis. This probe's *purpose* is to make the R2/brief
  guard mechanical: if any irreducibility field appears, the probe's type no longer matches the
  data-only consumer.

*First probe to land:* **P-RESID's `IsCyclotomicRestrictionIrreducible` half** — gate-independent,
`#print axioms`-clean, and it *names* the R2 distinction in Lean.

---

## 9. FIRST BUILDABLE SLICE + BOUNDED LATER BUILD UNITS

**First buildable slice (kernel-clean, gate-independent, retires a real edge):**
`def IsCyclotomicRestrictionIrreducible` (§5 A1) in **new** `FLT/ModularityLifting/ResidualImage.lean`
(matches `expected_module`). Imports `FLT.Deformations.RepresentationTheory.GaloisRep` +
`Mathlib.NumberTheory.Cyclotomic.Basic`. It is a **definition**, elaborates today against FOUND
primitives, needs no upstream gate, and *mechanically retires the R2 conflation edge* by giving
"cyclotomic-restriction irreducibility" a name distinct from `GaloisRep.IsIrreducible`. Pair with
probe **P-RESID** (`#print axioms`). Secondary gate-independent unit: `linearDisjoint_of_compositum`
(A0) — but confirm ownership vs moret-bailly (which also claims it; Q5).

**Bounded later build units (dependency order; each gated as marked):**
- **U0 (now):** A1 `IsCyclotomicRestrictionIrreducible` def + P-RESID probe. *No gate.*
- **U1 (after G-MB primitive scoping):** `AuxiliaryFieldCondition` structure (field-pure) + P-AFC probe;
  the two-disjointness split lemma. *Predicate elaborates; existence bridge stays `sorry`.*
- **U2 (after G-MLT):** pin the exact residual coefficient field / semisimplified-reduction object;
  restate A1/Layer C at that coefficient (retires counterexample #7).
- **U3 (after G-CF; the G-IND core):** CM character + `Representation.ind` seed; **build the
  induced-irreducibility / character-ratio criterion** (NONE FOUND) — the ℓ₁ CM-seed theorem. Unbounded.
- **U4 (after AUX-CURVE data):** ℓ₂ auxiliary-curve residual restriction irreducibility using MB
  disjointness (Layer C second conjunct).
- **U5:** assemble `cyclotomicRestrictionIrreducible` package (both primes) + close P-RESID full theorem.
- **U6 (after G-MB source gate + G-CF):** `exists_auxiliary_curve` existence (moduli point + induced
  character + good reduction), producing data only.
- **U7:** `exists_auxiliaryField` existence bridge from `moret_bailly_point`.

Each unit is bounded by its named gate; none may proceed past its gate without operator authorization
(`build_gate: upstream-build-only`).

---

## 10. STOP-LOSS GATE

Halt and escalate at the **first** of these (several already tripped):
- **G-MLT tripped (missing source vocabulary).** Do not state `cyclotomicRestrictionIrreducible` or the
  `unramified` fields of `AuxiliaryFieldCondition` at a *generic* `ZMod`/coefficient pretending to be
  the Taylor-2018 residual object. Escalate: await `FLT-MLT-SOURCE` (MLT-SOURCE-CONTRACT.md).
- **G-MB tripped (missing moduli primitive + source text).** Do not assert `exists_auxiliary_curve` /
  `exists_auxiliaryField` existence. Escalate: inherited from `FLT-MORET-BAILLY` (UNCERTAIN).
- **G-CF tripped (class field theory absent).** Do not fabricate a reciprocity/CM-induction axiom to
  supply the mod-p inducing character. Escalate: await `FLT-CLASS-FIELD`.
- **G-IND (induced-irreducibility criterion absent).** May *start* (U3) but is unbounded; report scope
  before committing build tokens.
- **R2 tripwire (design-level, terminal).** If any reviewer proposes moving an irreducibility/adequacy
  clause into `exists_auxiliary_curve`, or substituting plain `IsIrreducible` for
  `IsCyclotomicRestrictionIrreducible`, or an `SL₂(F_p)`-image bridge — **halt** and reject; it violates
  the brief, R2, and the corrected route.
- **R4 tripwire (design-level, terminal).** If the local shape is set to split-completely / `IsSplit`,
  halt: the selected source (Taylor 2018) needs unramified.

---

## 11. DEFINITION OF READY (checklist)

| DoR item | State | Evidence |
|---|---|---|
| Source exactness | **PARTIAL / GATED** | blueprint clauses frozen (ch04overview L21–98); Taylor 2018 8-hyp list (MLT-SOURCE-CONTRACT.md); SRC-011 primary absent (G-MB); MLT vocabulary absent (G-MLT) |
| Hypothesis translation | **DONE (vs blueprint) / GATED (vs residual vocab)** | §3, §5; each clause mapped, gated pieces named |
| Proof outline | **NOT DONE** | `source-design.ndjson: proof_outline:false`; only strategy (§9 U-units) |
| Sublemma graph | **DONE (design-level)** | §4 transitively reduced; internal order AUX-LOCAL-FIELD→AUX-CURVE→RESIDUAL-IMAGE |
| Counterexample review | **DONE** | §7 (10 hostile cases incl. R2/R4/brief-cycle) |
| Library matches | **DONE** | §6 exact decls / NONE FOUND (incl. FLT-local `WeierstrassCurve.galoisRep`) |
| Elaborated signatures | **PARTIAL / GATED** | §5; A0/A1 elaborate today; Layers B/C gated pieces named |
| Signature probes | **SPECIFIED** | §8; P-RESID half landable now |
| DoR verdict | **BLOCKED** (matches `source-design.ndjson dor:BLOCKED`) | promote on G-MLT + G-MB (curve/field) and G-MLT+G-CF+G-IND (residual) |

---

## 12. OPEN QUESTIONS FOR SYNTHESIS (GPT-5.6 reviewer / operator)

1. **G-MLT routing:** may RESIDUAL-IMAGE / AUX-LOCAL-FIELD freeze their *predicates* at a placeholder
   residual coefficient now (U0/U1) and re-pin at U2 once `FLT-MLT-SOURCE` selects the exact
   semisimplified-reduction object — or must they wait for MLT-SOURCE entirely?
2. **Two-prime split provenance:** the ℓ₁/ℓ₂ split is methodology-layer (CONVERGENCE.md), not in the
   blueprint. Confirm the two-application `cyclotomicRestrictionIrreducible` package (not a single
   theorem) is the frozen shape.
3. **Good-reduction placement (Q3):** confirm good reduction is a clause of the AUX-CURVE **conclusion**
   (curve-relative), not a field of `AuxiliaryFieldCondition` (avoiding the forward reference), despite
   the obligation text bundling it into AUX-LOCAL-FIELD.
4. **G-IND scope:** authorize building the induced-irreducibility / character-ratio criterion (U3,
   unbounded) at this node, or split it into its own obligation?
5. **A0 ownership:** does `linearDisjoint_of_compositum` land here (FLT-413) or under moret-bailly
   (FLT-303), which also proposed it as its first slice?
6. **First slice acceptance:** accept `IsCyclotomicRestrictionIrreducible` (+ P-RESID) in
   `FLT/ModularityLifting/ResidualImage.lean` as the first kernel-clean, gate-independent unit that
   names the R2 distinction?
```
