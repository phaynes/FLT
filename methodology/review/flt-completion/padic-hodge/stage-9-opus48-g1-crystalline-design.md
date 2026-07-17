# G1 — `GaloisRep.IsCrystallineAt` via `D_cris`: Primary Source & Lean Design

**Verdict: `DECOMPOSE-FIRST`.**

**Task:** `task:fg-flt-ra-math-source-design-20260716` — design (read-only, difficulty 10) the first
open mathematical provider beneath the reviewed p-adic-Hodge Tier-1 vocabulary: G1, an exact
`GaloisRep.IsCrystallineAt` predicate backed by a *genuine* period-ring `D_cris` construction.

---

## Context

The reviewed Tier-1 weight/dual probe (`FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`, namespace
`FLTMethodology.Taylor2018`) is coefficient-independent and deliberately carries **no** crystalline
field — crystallinity is a documented Tier-2 gap (`AbstractWeightLocalData` comment: "Carries NO
crystalline field"). G1 is the first genuine mathematical provider under it. The controlling question
is whether a genuine `D_cris` can be constructed against the pin **now**.

**Pin (ground truth, read from disk):**
- `lean-toolchain`: `leanprover/lean4:v4.32.0-rc1`
- `lake-manifest.json`: mathlib `a3364faec42918fcd84a03a255b50570129f9ead` (dated 2026-07-13; a very
  recent master that already contains a *nascent* perfectoid stack).

---

## 1. Reusable period-ring / crystalline implementation in the pin — reconfirmed

**Crystalline cohomology ≠ crystalline Galois representations.** The pin has the *cohomology / algebra*
side but **not** the *Fontaine period-ring / representation* side:

| Object | Status at pin | Location |
|---|---|---|
| `B_dR^+`, `B_dR` | **EXISTS but scaffolding** | `Mathlib/RingTheory/Perfectoid/BDeRham.lean` (`BDeRhamPlus`, `BDeRham`) |
| Fontaine's θ, untilt | EXISTS | `Perfectoid/FontaineTheta.lean` (`fontaineTheta`), `Perfectoid/Untilt.lean` (`untilt`) |
| `Perfection`, `PreTilt`, `Tilt`, `ModP` | EXISTS (`Ring.Perfection` deprecated → `Perfection`) | `Mathlib/RingTheory/Perfection.lean` |
| `WittVector`, `WittVector.frobenius`, Isocrystals | EXISTS | `WittVector/Frobenius.lean:221`, `WittVector/Isocrystal.lean:113` (**cohomology side**) |
| Divided powers / PD-algebra | EXISTS | `RingTheory/DividedPowers/*`, `RingTheory/DividedPowerAlgebra/*` (**cohomology side**) |
| **`B_cris` / `A_cris`** | **ABSENT** | — |
| **crystalline Galois-rep predicate / `D_cris`** | **ABSENT** | — (repo-wide grep for `IsCrystalline`, `D_cris`, `Bcris` returns nothing in `.lean` sources) |

Critical facts driving the verdict:
- **`B_dR` is not `B_cris`.** Defining crystallinity via the existing `B_dR` would define *de Rham* /
  Hodge–Tate representations, which is mathematically wrong for G1 and would violate the spirit of the
  hostile checks (HT weights / de Rham are separate providers).
- Even `BDeRham.lean` is early scaffolding: its own TODOs record that θ is **not** extended to
  `BDeRhamPlus`, `B_dR^+` is **not** proven a DVR, and **`ker θ` principality is unproven** — and the
  period element `t` for `B_cris = A_cris[1/p][1/t]` depends on exactly that generator.
- The one existing FLT primitive, `GaloisRep.IsFlatAt` (`FLT/Deformations/RepresentationTheory/
  GaloisRep.lean:391`), is an **integral finite-flat** condition, **not** generic-fibre crystallinity
  (that is the separate **G4** provider — do not conflate).

**Conclusion:** the next p-adic-Hodge layer is **not a wrapper around an existing pinned API**. A
genuine `B_cris`/`D_cris` must be constructed; the perfectoid/Witt/PD stack is available as raw
material but the crystalline period ring itself does not exist at the pin.

---

## 2. Repository anchor types (ground truth)

- `GaloisRep` (`GaloisRep.lean:47-51`): `def GaloisRep := letI := moduleTopology A (Module.End A M);
  Γ K →ₜ* Module.End A M`, where `Γ K = Field.absoluteGaloisGroup K`. Universe: **`K : Type uK`
  explicit; all others `Type*`.** Context: `[Field K] [NumberField K]`, `A [CommRing A]
  [TopologicalSpace A]`, `M [AddCommGroup M] [Module A M]`.
- Local place = `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` (notation `Ω K`);
  `Kᵥ = v.adicCompletion K`; `𝒪ᵥ = v.adicCompletionIntegers K`. Local rep via
  `GaloisRep.toLocal (ρ) (v) : GaloisRep (v.adicCompletion K) A M` (`GaloisRep.lean:309`). The
  decomposition group is the full local `Γ Kᵥ`. No bespoke `LocalField`/`Place` type.
- Tier-1 probe declarations that G1 sits beneath: `AbstractWeightData` (indexed by **global**
  embeddings `F →+* AlgebraicClosure ℚ_[ℓ]`), `IsRegularWeightData`, `HodgeTateWeightsMatch`,
  `InFontaineLaffailleInterval`, `EllUnramifiedInIntegers`, `AbstractWeightLocalData`, `GaloisRepDual`,
  `weightTwo_fits_iff_two_lt`, `repeatedWeightTwo_not_regular`.

---

## 3. Smallest mathematically correct definitions needed (exposed, not hidden in a Prop)

Crystallinity is **local at a place `v | ℓ`** of a `ℚ_[ℓ]`-representation of `Γ Kᵥ`. The genuine
mathematics that must be exposed:

- **Coefficient field:** `ℚ_[ℓ]` (minimum), or a finite extension `E/ℚ_[ℓ]` viewed as a finite-dim
  `ℚ_[ℓ]`-space. `A` in `GaloisRep K A M` must be a topological `ℚ_[ℓ]`-algebra and `V := M` a finite
  free `ℚ_[ℓ]`-space after restriction of scalars.
- **Completion data at `v | ℓ`:** `Kᵥ = v.adicCompletion K`; residue field `k(v)` (finite);
  `K₀ = FractionRing (WittVector ℓ k(v))` (max unramified subfield, the `D_cris` scalar field);
  `C = ` completion of `Kᵥᵃˡᵍ`; `𝒪_C♭ = PreTilt 𝒪_C`.
- **`A_cris`:** p-adic completion of the divided-power (PD) envelope of `WittVector ℓ 𝒪_C♭` along
  `ker(fontaineTheta)`. **← the genuine, currently-absent core.**
- **Frobenius `φ`** on `A_cris` (from `WittVector.frobenius` / perfection Frobenius) and **period
  `t`** (generator of `ker θ`; upstream-blocked by the `BDeRham` `ker θ` principality TODO).
- **`B_cris = A_cris[1/p][1/t]`**, an `ℚ_[ℓ]`- and `K₀`-algebra with continuous `Γ Kᵥ`-action and
  `B_cris^{Γ Kᵥ} = K₀`.
- **`D_cris(V) := (B_cris ⊗_{ℚ_[ℓ]} V)^{Γ Kᵥ}`**, a `K₀`-vector space.
- **Crystalline:** `finrank K₀ (D_cris V) = finrank ℚ_[ℓ] V` (always `≤`; crystalline = equality).

None of `B_cris`, `φ`, `t`, `D_cris` may be a bare `Prop` field — each is a construction/theorem node
below.

---

## 4. Proposed Lean signatures (universe-polymorphic, at repo types)

### 4a. TARGET SHAPE — **NOT bankable now** (requires genuine `B_cris`)

```lean
namespace FLTMethodology.Taylor2018
open IsDedekindDomain

/-- G1 target. `v` must lie above `ℓ`; `A` must be a `ℚ_[ℓ]`-algebra. NOT DEFINABLE at the pin:
    depends on a genuine `B_cris`, absent from mathlib a3364fa. -/
def GaloisRep.IsCrystallineAt
    {K : Type uK} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (v : HeightOneSpectrum (𝓞 K)) : Prop := ...
```

### 4b. SMALLEST SAFE BUILD UNIT — bankable now, honest, trio-clean

The relative (period-ring-parameterized) `D`-functor. It exposes real fixed-point mathematics and
**does not claim crystallinity**; the true predicate is obtained only by instantiating `B := B_cris`
(the deferred provider). This is the correct answer to the "do not hide the theorem in a Prop" check.

```lean
/-- Place above the rational prime ℓ (crystalline theory only applies here). -/
def IsPlaceAbove (ℓ : ℕ) {K : Type uK} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  (ℓ : 𝓞 K) ∈ v.asIdeal

/-- The `D`-functor of ANY coefficient ring `B` carrying a `Γ`-action:
    the `Γ`-invariants of `B ⊗[E] V`. Honest fixed-point mathematics; NOT crystalline. -/
noncomputable def periodModule
    (Γ : Type*) [Group Γ]
    {E : Type*} [CommRing E]
    (B : Type*) [CommRing B] [Algebra E B] [MulSemiringAction Γ B]
    {V : Type*} [AddCommGroup V] [Module E V] [DistribMulAction Γ V]
    -- diagonal Γ-action on B ⊗[E] V; invariants as a submodule over the fixed ring Bᴳ
    : Submodule (FixedPoints.subring Γ B) (B ⊗[E] V) := ...

/-- Crystallinity RELATIVE to a supplied period ring `B` and scalar field `K₀ = Bᴳ`.
    Becomes G1's `IsCrystallineAt` exactly when `B := B_cris`. -/
def IsCrystallineRel
    (Γ : Type*) [Group Γ] {E : Type*} [Field E]
    (B : Type*) [CommRing B] [Algebra E B] [MulSemiringAction Γ B]
    (V : Type*) [AddCommGroup V] [Module E V] [Module.Finite E V] [DistribMulAction Γ V] : Prop :=
  Module.finrank (FixedPoints.subring Γ B) (periodModule Γ B V)
    = Module.finrank E V
```

**Minimum coefficient/completion data:** `E = ℚ_[ℓ]`; `Γ = Γ Kᵥ` (full local Galois group of
`v.adicCompletion K` for `v | ℓ`); `K₀ = Bᴳ = FractionRing (WittVector ℓ (residue field))`. To reach
the honest G1 predicate one supplies `B := B_cris` over `C`.

---

## 5. Dependency graph (routine infra vs genuine provider theorem)

Legend: **[I]** routine Lean infrastructure · **[P]** genuine mathematical provider theorem ·
`d=` estimated difficulty.

```
Tier-1 weight/dual probe  (LANDED)
  │
  ├─ N0 [I] IsPlaceAbove ℓ v + local rep restriction (toLocal)          d=3
  │        src: HeightOneSpectrum (DedekindDomain/Ideal/Lemmas.lean:495), GaloisRep.toLocal:309
  │
  ├─ N1 [I] periodModule: diagonal Γ-action on B⊗[E]V, invariants submod d=6   ◄ FIRST BANKABLE
  │        src: TensorProduct(.congr Map.lean:248/Tower.lean:322), MulSemiringAction
  │             (Ring/Action/Basic.lean:51), FixedPoints (FieldTheory/Fixed.lean:103)
  │
  ├─ N2 [I] IsCrystallineRel (finrank equality over Bᴳ)                  d=2
  │        src: Module.finrank (Dimension/Finrank.lean:62), finrank_tensorProduct (Constructions:375)
  │
  ▼  ─────────────── genuine provider region (BLOCKED at pin) ───────────────
  ├─ N3 [P] A_cris = p-completed PD-envelope of W(𝒪_C♭) along ker θ       d=9
  │        src: PreTilt/Perfection.lean, fontaineTheta (FontaineTheta.lean),
  │             DividedPowers/DividedPowerAlgebra, IsAdicComplete (AdicCompletion/Basic.lean)
  │        RISK: needs PD-envelope-of-ideal (verify presence in DividedPowers/*)
  ├─ N4 [P] Frobenius φ on A_cris                                        d=8   (src: WittVector.frobenius:221)
  ├─ N5 [P] period t = generator of ker θ / log[ε]                       d=8   ◄ upstream-blocked by BDeRham `ker θ` TODO
  ├─ N6 [P] B_cris = A_cris[1/p][1/t] + continuous Γ Kᵥ-action           d=8   (src: Localization.Away, ContinuousSMul)
  ├─ N7 [P] B_cris^{Γ Kᵥ} = K₀  (scalar-field identification)            d=9
  ├─ N8 [P] D_cris comparison: dim ≤ always; crystalline ⇔ equality      d=10
  └─ N9 [I] GaloisRep.IsCrystallineAt := IsCrystallineRel with B:=B_cris  d=4  (assembly)
```

Source boundaries: N0–N2 sit entirely on landed Mathlib/FLT APIs. N3–N8 are the Fontaine period-ring
mathematics absent from the pin; N5/N7 in particular depend on results Mathlib itself lists as open
TODOs. **Controlled upgrade path:** track upstream Mathlib PRs extending `Perfectoid/*` (θ on
`BDeRhamPlus`, `ker θ` principality, `A_cris`); adopt only when the exact reusable declarations exist,
never speculatively.

---

## 6. `#check` / axiom probes — read-only status

Plan mode forbids non-read-only Lean invocation (`lake build` / `lake env lean` write build
artifacts), consistent with stage-7's own note. **No live `#check`/`#print axioms` was executed.**
Instead, every "existing" declaration cited above was read directly from the pinned source on disk
(read-only equivalent of a `#check`): `GaloisRep`/`toLocal`, `HeightOneSpectrum`, `adicCompletion`,
`BDeRhamPlus`/`BDeRham`, `fontaineTheta`, `Perfection`/`PreTilt`/`Tilt`, `WittVector.frobenius`,
`FixedPoints.subfield`, `MulSemiringAction`, `TensorProduct.congr`, `Module.finrank`,
`Module.finrank_tensorProduct`, `IsAdicComplete`.

The proposed bankable slice (N0–N2) depends **only** on standard Mathlib defs — none in
`FLT/KnownIn1980s`, none carrying a custom axiom — so it is standard-trio-clean **by construction**.
**Acceptance gate (must run at build, outside plan mode):** every bankable declaration must
`#print axioms` to exactly `[propext, Classical.choice, Quot.sound]` with **no** `sorryAx`,
`knownin1980s`, or custom axiom; any deviation → REVISE with the failing declaration. Kernel output is
authoritative.

---

## 7. Decision, smallest safe build unit, first residual goal

**A bounded first production slice exists, but the full G1 predicate cannot be responsibly defined
against the pin** (`B_cris` genuinely absent; genuine construction is a multi-theorem provider N3–N8,
partly blocked by Mathlib's own open TODOs). Therefore **`DECOMPOSE-FIRST`**, not `DESIGN-VIABLE`
(no genuine `D_cris` now) and not `OBSTRUCTION` (a real, safe first slice and a path both exist).

- **Smallest safe build unit:** N0 + N1 + N2 — `IsPlaceAbove`, `periodModule` (the `(B⊗V)^Γ`
  D-functor over an *exposed* period-ring parameter), and `IsCrystallineRel`. Honest (does not assert
  crystallinity), reusable by every later node, trio-clean.
- **First residual goal:** in N1, construct the diagonal `Γ`-action on `B ⊗[E] V` from
  `MulSemiringAction Γ B` and `DistribMulAction Γ V`, and prove the invariants are closed under
  `Bᴳ`-scaling so `periodModule` is a well-formed `Submodule (FixedPoints.subring Γ B) (B ⊗[E] V)`.
- **First genuine provider to schedule after infra:** N3 `A_cris` (verify PD-envelope-of-ideal exists
  in `RingTheory/DividedPowers/*` first), then N4→N8, then N9 assembly. This matches stage-6's
  proposed 6-step decomposition and the stage-4 G-node order G1→G2→G4.

### Hostile checks honored
- No abstract `IsCrystalline` Prop field: crystallinity is `finrank`-of-fixed-points content, and the
  bankable predicate is explicitly *relative* to an exposed `B`, not a hidden theorem.
- Global embeddings (`F →+* AlgebraicClosure ℚ_[ℓ]`, Tier-1) kept distinct from local places `v | ℓ`
  (`IsPlaceAbove`, N0); crystallinity is defined only at `v | ℓ`.
- Finite-flat (`IsFlatAt`, integral) NOT assumed to imply crystalline — that is the separate **G4**
  provider, explicitly excluded here.
- No HT weights / Fontaine–Laffaille bounds claimed from crystallinity; those are G2 and the Tier-1
  interval respectively.
- No reliance on un-pinned APIs: `B_dR`/perfection/θ are cited at the exact pin (a3364fa); `B_cris`
  is acknowledged absent with a controlled upgrade path, not assumed.
- Standard-trio target preserved for all produced infrastructure (N0–N2), gated at build.

---

## Verification (when execution is authorized, outside plan mode)
1. Add N0–N2 to a probe file in `FLTMethodology/Probes/` under `namespace FLTMethodology.Taylor2018`.
2. Targeted `lake build` of that module; then `#print axioms` on each new declaration — require
   exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
3. Instantiate `periodModule`/`IsCrystallineRel` on a toy `B` (e.g. `E` itself, trivial action) to
   confirm the finrank equality reduces sensibly (sanity, not crystallinity).
4. Do **not** promote `GaloisRep.IsCrystallineAt` until N3–N8 land.
