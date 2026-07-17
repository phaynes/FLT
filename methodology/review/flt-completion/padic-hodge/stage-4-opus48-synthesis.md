# FLT-MLT-PADIC-HODGE — Opus 4.8 post-diversity synthesis (difficulty 10)

## Context

Obligation `FLT-MLT-PADIC-HODGE` owns the local/Hodge-theoretic hypotheses of Taylor 2018 Thm 2.1.1
(p.12): matching Hodge–Tate weights, `ℓ` unramified in the totally-real base `F`, crystallinity at
every `v | ℓ`, the Fontaine–Laffaille interval, regular weight data, and the weight-two
finite-flat→crystalline bridge. Three prior stages disagree on three load-bearing points; this
synthesis freezes **one** source- and Lean-exact design and independently re-verifies each dispute
against the pinned repository APIs.

**This document is read-only design.** No repository file is edited, no probe is built here, no
axiom is registered, no obligation is promoted. All "elaborated" claims below are the diversity
chain's machine checks (stages 2/3); my own verification is by inspection against the pinned APIs,
listed with file:line. Acceptance still requires re-running `#print axioms` on the persisted probe.

Pins: Lean `v4.32.0-rc1`, Mathlib `a3364faec42918fcd84a03a255b50570129f9ead`.

### Three adjudications (independently verified)

1. **Global vs local weight indexing** — ADJUDICATED GLOBAL. Opus stage-1 indexed by embeddings of a
   completion into its own abstract closure; GPT stage-2 + Fable stage-3 corrected to Taylor's global
   embeddings `F →+* AlgebraicClosure ℚ_[ℓ]`. Confirmed: this is Taylor's normalization and the only
   spelling that admits one global interval base `a`.
2. **`{-1,0}` at `ρ` vs dual `{0,1}`** — ADJUDICATED `{-1,0}` at `ρ`, `{0,1}` at `GaloisRepDual ρ`.
   Independently verified the forcing convention: `IsHardlyRamified.det` pins
   `ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter … g)` (`FLT/GaloisRepresentation/HardlyRamified/Defs.lean:107`;
   same at `FLT/ModularityLifting/Conditions.lean:37-38`, `FLT/Deformations/LiftFunctor.lean:150`).
   With Taylor's `HT(ε) = -1`, the weight sum equals `HT(det ρ) = HT(ε) = -1`; a regular weight-two
   multiset of consecutive integers summing to `-1` is `{-1,0}`. The étale-H¹/dual side negates to
   `{0,1}`. Opus stage-1's bridge concluded `{0,1}` **at `ρ`** — that is the sign regression this
   design rejects.
3. **Integral vs generic-fibre separation** — ADJUDICATED SEPARATED. `GaloisRep.IsFlatAt` carries
   `[IsLocalRing A]` and reduces through `HasFlatProlongationAt`, which requires finite cardinality of
   the reductions (`FLT/Deformations/RepresentationTheory/GaloisRep.lean:383-393`). Over a char-0
   field `E = AlgebraicClosure ℚ_[ℓ]` it typechecks (a field is a local ring) but is essentially
   vacuous. Flatness therefore attaches to the integral model `ρ₀ : GaloisRep F O V₀`; crystallinity
   is concluded at the generic `ρ`. Opus stage-1 used one `ρ` for both — rejected by GPT stage-2.

---

## Pinned API ground truth (verbatim, with file:line)

- `GaloisRep K A M := Γ K →ₜ* Module.End A M`, `[Field K] [NumberField K] [CommRing A]
  [TopologicalSpace A] [AddCommGroup M] [Module A M]`; `ρ σ : Module.End A M = M →ₗ[A] M`
  (`GaloisRep.lean:47-59`). Universe: only `K : Type uK` explicit.
- `GaloisRep.conj (ρ) (e : M ≃ₗ[A] N) : GaloisRep K A N` (`:96-103`).
- `GaloisRep.baseChange (B) [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
  [Module.Finite A M] [Module.Free A M] (ρ) : GaloisRep K B (B ⊗[A] M)` (`:206-224`).
- `GaloisRep.det (ρ) : Γ K →ₜ* A` from `LinearMap.det ∘ ρ` (`:200-204`).
- `GaloisRep.IsFlatAt [IsLocalRing A] (ρ) : Prop` at section var `v : Ω K` (`:389-393`).
- `Ω K := IsDedekindDomain.HeightOneSpectrum (𝓞 K)`; place has `.asIdeal : Ideal (𝓞 K)` (`:42`).
- **No dual/contragredient exists anywhere in `FLT/`** — `GaloisRepDual` must be built here.
- `GaloisRep.IsAutomorphicOfLevel … (S : Finset (Ω F))` body guards good primes only:
  `∀ v, ↑p ∉ v.1 → v ∉ S → …` (`FLT/GaloisRepresentation/Automorphic.lean:69-97`, guard at `:90`).
- `Algebra.IsUnramifiedIn (A) [Algebra R A] (𝔭 : Ideal R) : Prop`
  (`Mathlib/RingTheory/Unramified/Locus.lean:98`).
- Probe pattern: `FLTMethodology/Probes/MLTSourceBoundary.lean` — plain `import` (not `module`),
  `namespace FLTMethodology.Taylor2018`, `def … : Prop`, then `#check` + `#print axioms` per decl;
  register in `FLTMethodology.lean`. `FLT-MLT-COEFFICIENTS` probe (`MLTCoefficientData.lean`) **does
  not exist yet** — coefficients have not landed.
- **Embedding-indexing precedent:** `GaloisRepFamily` already indexes by
  `(φ : E →+* AlgebraicClosure ℚ_[p])` and pairs `v.asIdeal` with `IsUnramifiedAt`
  (`FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean:38-64`). This validates the
  `F →+* AlgebraicClosure ℚ_[ℓ]` weight indexing as the repo idiom. Note the source subtlety: the repo
  family indexes by embeddings of the *coefficient* number field `E`; Taylor's HT weights are indexed
  by embeddings of the *base* totally-real field `F` — so `AbstractWeightData`'s domain is
  `F →+* AlgebraicClosure ℚ_[ℓ]` with `[NumberField F]`, not the coefficient field.
- **Prime-in-place idiom:** membership is spelled with the ℕ-cast into the ring of integers,
  `(ℓ : 𝓞 F) ∈ v.asIdeal` (cf. `(p : 𝓞 K) ∉ v.asIdeal` at `GaloisRepFamily.lean:64`); `𝓞 F` =
  `NumberField.RingOfIntegers F`. `Algebra.IsUnramifiedIn` lives in `namespace Algebra`.

---

## Deliverable 1 — First no-axiom weight-data / dual probe (exact signatures)

New file `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`, `namespace FLTMethodology.Taylor2018`,
plain imports (`FLT.Deformations.RepresentationTheory.GaloisRep`, `Mathlib.RingTheory.Unramified.Locus`,
`Mathlib.LinearAlgebra.Dual.Lemmas`). This slice is **coefficient-independent** (Fable finding): it
names no `ρ`-level crystalline/HT/finite-flat symbol, so it may land before `FLT-MLT-COEFFICIENTS`.

```lean
/-- Global Hodge–Tate weight datum, indexed by Taylor's global ℓ-adic embeddings of F. -/
def AbstractWeightData
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  (F →+* AlgebraicClosure ℚ_[ℓ]) → Multiset ℤ

/-- Regularity: full cardinality = rank AND distinct weights at every global embedding. -/
def IsRegularWeightData
    {F : Type*} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime]
    (rank : ℕ) (w : AbstractWeightData F ℓ) : Prop :=
  ∀ τ : F →+* AlgebraicClosure ℚ_[ℓ], (w τ).card = rank ∧ (w τ).Nodup

/-- Pointwise weight matching at every global embedding. -/
def HodgeTateWeightsMatch
    {F : Type*} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime]
    (w₁ w₂ : AbstractWeightData F ℓ) : Prop :=
  ∀ τ : F →+* AlgebraicClosure ℚ_[ℓ], w₁ τ = w₂ τ

/-- Fontaine–Laffaille interval: `ℓ - 1` CONSECUTIVE integers `[a, a+ℓ-2]`, one GLOBAL base `a`.
    (GPT/Fable correction: this is NOT a diameter-`ℓ-1` condition.) -/
def InFontaineLaffailleInterval
    {F : Type*} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime]
    (a : ℤ) (w : AbstractWeightData F ℓ) : Prop :=
  ∀ τ : F →+* AlgebraicClosure ℚ_[ℓ], ∀ n ∈ w τ, n ∈ Set.Icc a (a + (ℓ : ℤ) - 2)

/-- `ℓ` is unramified in F, using the source-level ramification predicate (R = ℤ). -/
def EllUnramifiedInIntegers
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ : ℤ)})

/-- ρ-free Galois-side local data bundle. Carries NO crystalline field (that is a Tier-2 gap). -/
structure AbstractWeightLocalData
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (rank : ℕ) where
  weights        : AbstractWeightData F ℓ
  regular        : IsRegularWeightData rank weights
  intervalBase   : ℤ
  inInterval     : InFontaineLaffailleInterval intervalBase weights
  ellUnramified  : EllUnramifiedInIntegers F ℓ

/-- Contragredient. `σ⁻¹` makes `dualMap` (contravariant) a genuine monoid hom:
    `ρ((στ)⁻¹).dualMap = ρ(τ⁻¹σ⁻¹).dualMap = (ρσ⁻¹).dualMap ∘ (ρτ⁻¹).dualMap`, matching `*` in
    `Module.End`. Finite/free binders match `baseChange`'s and are needed for continuity of `dualMap`
    under the module topology. -/
noncomputable
def GaloisRepDual
    {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K A (Module.Dual A M) :=
  -- term: σ ↦ (ρ σ⁻¹).dualMap, packaged as a Γ K →ₜ* Module.End A (Module.Dual A M)
  …
```

Plus two guard lemmas (Deliverable 5) and, per-decl, `#check` + `#print axioms`.

**Single elaboration-risk item:** `GaloisRepDual`'s `ContinuousMonoidHom` packaging (continuity of
`dualMap` under the module topology). Fable stage-3 reports it elaborated with the standard trio; I
did not rebuild it. If continuity resists at char-0 generality, fall back to the framed/matrix route
(transpose-inverse via `FramedGaloisRep.GL`) or defer the dual to the bridge probe — the weight
vocabulary above stands regardless.

---

## Deliverable 2 — Later bridge context consuming the reviewed coefficient bundle

DEFERRED until `FLT-MLT-COEFFICIENTS` lands (its probe file does not yet exist). Stated as the
mathematical target shape only; `IsCrystallineAt` / `hodgeTateWeightsAt` remain Tier-2 gaps (G1/G2),
so this is a documented graph gap, **not** a compiling declaration and **not** an opaque placeholder.

```lean
-- TARGET SHAPE ONLY — not to be persisted until coefficients + period rings exist.
theorem GaloisRep.isCrystalline_of_isFlatAt_weightTwo
    {F : Type*} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 2 < ℓ)
    {O : Type*} [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
      /- finite residue field, adic-complete: the T-A2 consumer requirements -/
    {E : Type*} [Field E] [Algebra O E] /- E ≈ generic fibre / AlgebraicClosure ℚ_[ℓ] -/
    {V₀ : Type*} [AddCommGroup V₀] [Module O V₀] [Module.Finite O V₀] [Module.Free O V₀]
      (hrank : Module.rank O V₀ = 2)
    {V : Type*} [AddCommGroup V] [Module E V]
    (ρ₀ : GaloisRep F O V₀) (ρ : GaloisRep F E V)
    (iso : E ⊗[O] V₀ ≃ₗ[E] V)
    (compat : (ρ₀.baseChange E).conj iso = ρ)          -- reuses GaloisRep.baseChange / .conj
    (v : Ω F) (hv : (ℓ : 𝓞 F) ∈ v.asIdeal)
    (hflat : ρ₀.IsFlatAt v) :                           -- flatness on the INTEGRAL model
    ρ.IsCrystallineAt v ∧
      (∀ τ, ρ.hodgeTateWeightsAt v τ = {-1, 0})          -- {-1,0} at ρ (det ρ = ε)
```

Consumed coefficient bundle: exactly the `StableLatticeData`/`HasIntegralModel` shape from the
coefficients synthesis — a finite-free rank-two `V₀`, `ρ₀`, generic-fibre `iso`, and
`(ρ₀.baseChange E).conj iso = ρ`. Dual transport (G6): from this, `GaloisRepDual ρ` is crystalline at
`v` with `hodgeTateWeightsAt v τ = {0, 1}` — the étale-H¹ side. No period-ring predicate is invented
before `D_HT`/`D_cris` exist.

---

## Deliverable 3 — Honest owners

| Concern | Node | Owner / status |
|---|---|---|
| `GaloisRep.IsCrystallineAt` | G1 | Tier-2, this obligation; needs period-ring `D_cris`. Documented gap; no placeholder Prop. |
| Hodge–Tate weight extraction (`hodgeTateWeightsAt`) | G2 | Tier-2, this obligation; under the pinned `det ρ = ε` sign. Documented gap. |
| Finite-flat → crystalline weight-two comparison | G4 | Tier-2, this obligation; **dominant risk** (Raynaud / Fontaine–Laffaille / Breuil–Kisin). Uses `ρ₀.IsFlatAt` (integral). |
| Global-embedding → ℓ-adic place mapping | G5 | Tier-2, this obligation; `F →+* AlgebraicClosure ℚ_[ℓ]` ↔ `v : Ω F` inside weight extraction. |
| Dual transport (weights + crystallinity) | G6 / G6′ | This obligation; consumes `GaloisRepDual` (Deliverable 1) once G1/G2 exist. `{-1,0} → {0,1}`. |
| Determinant-weight guard (Σ weights = det weight) | G7 | This obligation; guards sign regression against `det ρ = ε` (`HardlyRamified/Defs.lean:107`). |

Automorphic-side `π_v` unramifiedness for `v | ℓ` is **NOT** in this Galois-side bundle — owned by
RACAR/source (Deliverable 4).

---

## Deliverable 4 — RACAR dependency / interface consequences

- **`IsAutomorphicOfLevel` cannot carry at-ℓ unramifiedness.** Its body only constrains good primes
  `v` with `↑p ∉ v.1` and `v ∉ S` (`Automorphic.lean:90`). So Taylor hypothesis 7 (`π_v` unramified
  at every `v | ℓ`) must be an **explicit** field of the RACAR/source interface, never inferred from
  `IsAutomorphicOfLevel … ∅`. Crystallinity of `ρ` is not Galois unramifiedness at `ℓ`, and neither is
  the automorphic condition — three distinct facts.
- **RACAR consumes this node's weight vocabulary.** `FLT-RACAR-DEF` needs `AbstractWeightData`,
  `IsRegularWeightData`, and `HodgeTateWeightsMatch` to state the weight datum attached to `π` and the
  `π/ρ` weight match. Therefore RACAR cannot be frozen until this Tier-1 probe is kernel-green.
- **Dependency order (revised, splitting Tier-1 from the bridge):**
  ```
  FLT-MLT-COEFFICIENTS
    → p-adic-Hodge Tier-1 weight/dual probe   (INDEPENDENT of coefficients — may land in parallel/now)
    → p-adic-Hodge Tier-2 (crystalline/HT/place map) + weight-two bridge   (needs coefficients + period rings)
    → FLT-RACAR-DEF                            (needs the Tier-1 weight vocabulary)
    → FLT-MLT-SOURCE                           (needs Galois-side weights HERE + automorphic-side unramifiedness in RACAR)
    → FLT-SGOOD-SELECTED and MLT consumers
  ```
- **Consumer ledger correction preserved:** p-adic-Hodge, RACAR, SelectedGood are **not** current
  compiled consumers (those declarations do not exist in `FLT/`). Live consumers of the coefficient
  side are `GaloisRep.IsAutomorphicOfLevel`, `GaloisRepresentation.IsHardlyRamified.lifts`, and
  `Deformation.ProartinianCat` representability.

---

## Deliverable 5 — Temporary-probe results, counterexamples, smallest slice

### Probe results (diversity chain; not re-run here)
- GPT stage-2: corrected data-only bundle over `(F →+* AlgebraicClosure ℚ_[ℓ]) → Multiset ℤ` with
  regularity, pointwise matching, interval `[a, a+ℓ-2]`, and `Algebra.IsUnramifiedIn` elaborated with
  exactly `[propext, Classical.choice, Quot.sound]`.
- Fable stage-3: full Tier-1 vocabulary + `GaloisRepDual (σ ↦ (ρ σ⁻¹).dualMap)` + both guard lemmas
  elaborated with exactly the standard trio.
- My check: every signature above matches the pinned API surface (`GaloisRep.lean`,
  `Automorphic.lean`, `Unramified/Locus.lean:98`, `HardlyRamified/Defs.lean:107`). **Not rebuilt**
  (read-only). Acceptance = targeted build + `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.

### Counterexamples / guards (persist the first two as lemmas)
- **G-A (`2 < ℓ` load-bearing):** `{-1,0} ⊆ Set.Icc a (a+ℓ-2)` needs `a ≤ -1` and `a+ℓ-2 ≥ 0`, i.e.
  `2-ℓ ≤ a ≤ -1`, nonempty only for `ℓ ≥ 3`. `ℓ = 2` (interval a single point) is a concrete
  counterexample that regular weight-two cannot inhabit. Persist as a guard lemma.
- **G-B (regularity rejects `{0,0}`):** `({0,0} : Multiset ℤ)` is not `Nodup`, so
  `IsRegularWeightData 2` fails. Persist as a guard lemma. Also `{0,1,2}` fails card = 2.
- **G-C (sign regression, G7):** the false `{0,1}`-at-`ρ` design gives Σ = 1 ≠ `HT(det ρ) = HT(ε) = -1`.
  The determinant-weight guard rejects it; independently traced to `det ρ = ε` at
  `HardlyRamified/Defs.lean:107` and `ModularityLifting/Conditions.lean:37`.
- **G-D (flatness vacuity):** `ρ.IsFlatAt v` over `E = AlgebraicClosure ℚ_[ℓ]` typechecks (field is
  local) but `HasFlatProlongationAt` forces finite reductions → vacuous. Flatness must be on `ρ₀`.
  (No lemma; this is the structural reason Deliverable 2 separates `ρ₀`/`ρ`.)

### Smallest production slice
`FLTMethodology/Probes/MLTPadicHodgeWeightData.lean` containing ONLY: `AbstractWeightData`,
`IsRegularWeightData`, `HodgeTateWeightsMatch`, `InFontaineLaffailleInterval`,
`EllUnramifiedInIntegers`, `AbstractWeightLocalData`, `GaloisRepDual`, guard lemmas G-A and G-B, and
`#check` + `#print axioms` per declaration; then register `import FLTMethodology.Probes.MLTPadicHodgeWeightData`
in `FLTMethodology.lean` (near line 21). NO crystalline / HT / finite-flat / period-ring symbol
appears. The bridge (Deliverable 2) is persisted only after coefficients land.

---

## Deliverable 6 — Verdict

**READY-FOR-GPT-REVIEW (conditioned).**

The design is source- and Lean-exact: global weight indexing, the `[a, a+ℓ-2]` interval,
`Algebra.IsUnramifiedIn`, the `{-1,0}`-at-`ρ` / `{0,1}`-at-dual adjudication (forced by the verified
`det ρ = ε`), and integral/generic separation are all settled and consistent with the pinned APIs.
The smallest slice is a coefficient-independent weight/dual probe that can land now.

Conditions (nothing here promotes the obligation; it stays a definition gap):
1. GPT re-review confirms the five interface questions are closed as above (global indexing,
   `[a,a+ℓ-2]`, RACAR-owned automorphic unramifiedness, abstract weights until `D_HT`,
   `Algebra.IsUnramifiedIn`).
2. The persisted probe contains only the Deliverable-1/5 vocabulary; every `#print axioms` returns
   `[propext, Classical.choice, Quot.sound]` with no `sorryAx` — in particular `GaloisRepDual`
   re-audits clean (the one elaboration risk).
3. Tier-2 (G1/G2/G4/G5/G6/G7) and the weight-two bridge remain documented gaps; the bridge probe is
   persisted only after `FLT-MLT-COEFFICIENTS` lands.

## Verification (how to check this design when execution is authorized)
1. Create the probe file; `lake build FLTMethodology.Probes.MLTPadicHodgeWeightData`.
2. Read the `#print axioms` output for each of the 7 defs + 2 guard lemmas; require exactly the trio.
3. Confirm `GaloisRepDual` needs no `sorryAx`; if it fails continuity, apply the framed fallback.
4. Leave `IsCrystallineAt`/`hodgeTateWeightsAt`/bridge unbuilt (graph gaps) until coefficients land.
