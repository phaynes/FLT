# Stage 1 primary design — Opus 4.8

## Model and transport evidence

- Agent: `opus48-primary-designer-d8`
- Configured model: `claude-opus-4-8`
- Backend transport: `claude-code`
- Role: `primary`
- Difficulty: `8/10`
- Scheduled design budget: `3000 s`
- Exit code: `0`
- Actual invocation elapsed: `669147 ms`
- Claude session: `89186f12-5a49-417d-bef5-e7e0e9c682cb`
- Token audit: `46` unique provider request IDs across the primary session and its subagents
- Input tokens: `55,078`
- Cache-creation input tokens: `281,398`
- Cache-read input tokens: `2,394,660`
- Output tokens: `37,978`
- Total tokens including cache traffic: `2,769,114`
- Output characters returned through bridge: `1289`
- Full design-report characters recovered from Claude plan artifact: `29692`
- Bridge topology: `single`
- Bridge total duration: `669147 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/tate-frey/stage-1-prompt-opus48-primary.md`
- Repository mutation authority: read-only; no model repository edits permitted
- Claude plan source: `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-typed-fog.md` (copied verbatim below into the governed component evidence)

## Bridge completion message

The `ExitPlanMode` tool is not available in this session's toolset, so I'll conclude here — the deliverable is complete.

**Delivered:** the full Stage-1 primary design report at `~/.claude/plans/primary-opus-4-8-design-typed-fog.md`, satisfying the 11-section output contract from `stage-1-prompt-non-fable.md` (adapted to the Opus-primary verdict set), produced entirely read-only with zero repository edits.

**Verdict returned:** `READY-FOR-GPT-REVIEW` — the five live obligations and their join are decomposed into bounded, kernel-checkable build units; the two proved obligations are preserved as regressions; every claim is verified against source (all seven control rows, the four consumer fields, the ten `TateCurve.lean` admissions, and the Mathlib NONE-FOUND set); and the two genuine obstructions (`isFlat` at the residue characteristic, and a nonzero Weil pairing) are precisely located, staged behind approved sources, and flagged for the reviewer's build-vs-named-gate decision rather than papered over.

The single open decision I could not resolve read-only, and which the GPT reviewer must rule on: **build the finite-flat-scheme and Weil-pairing theories, or carry each as a named source gate** (SRC-023/025) under T1 policy. That is question 1 in the report's §11.

## Full primary design report

# PRIMARY OPUS 4.8 DESIGN — TATE–FREY REMAINING CLUSTER (Stage 1)

**Role:** first-attempt primary producer under the Opus-first ladder. Read-only. Independent design.
**Repo:** `/Volumes/second-store/devel/proof-forks/FLT`  ·  work-order SHA `827eb96`.
**Verdict (routing):** `READY-FOR-GPT-REVIEW` — see §VERDICT for the bounded obstruction ledger.

> NOTE: This file is the design report, not an implementation. No proof here is complete until it is
> kernel-checked. A source citation, a methodology probe, a scaffold, or a `sorry` is **not** a
> provider. Two sub-slices (`isFlat` at the residue characteristic, and a nonzero Weil pairing) bottom
> out in Mathlib APIs that do **not exist**; they are staged behind approved sources SRC-023/024/025
> and flagged for a named-assumption decision by the GPT reviewer.

---

## 1. VERDICT — `READY-FOR-GPT-REVIEW`

The five live obligations decompose cleanly into bounded, kernel-checkable build units, the two
already-proved obligations (`FLT-TATE-TORSION`, `FLT-TORSION-001`) are preserved as regressions and
never reopened, and there exist first tranches that are closeable **now** with no absent API. No
statement in the target consumer `IsHardlyRamified` is false, and no route below requires an
unapproved named assumption. The design is therefore reviewable.

However this is **not** a clean "ready to close": two cores hit the stop-loss gate *absent
foundational API*. (a) The `isFlat` field at `ℓ = P.p` when `ℓ ∣ abc` (multiplicative reduction) and
the honest good-reduction case at `n = p` both require a **finite flat group-scheme / Hopf-algebra
model at the residue characteristic** that Mathlib does not have beyond the raw `HopfAlgebra` typeclass
— there is no `E[n]`-as-group-scheme, no Katz–Mazur "×n is finite locally free," no Cartier duality.
(b) `FLT-TATE-WEIL` requires a **source-faithful nonzero/perfect alternating Galois-equivariant Weil
pairing**; Mathlib has no Weil pairing, no Miller functions, no divisor/Picard machinery, and the
current `weilPairing` type is inhabited by the zero map. These are correct statements with **no
library leaf**; they are genuine new theory, not scaffolding to be filled. The GPT reviewer must
decide per T1 policy whether they are built or carried as named source gates.

Everything else — the whole `TateCurve` uniformization chain, unramifiedness away from `2ℓ`, the
cyclotomic determinant, the tame-at-2 quotient, and the `FLT-SUPPORT-TATE` join — is bounded, has an
exact signature, and rests on approved sources.

---

## 2. CURRENT EXACT BOUNDARY

### 2.1 Already-proved regressions (PRESERVE — do not reopen)

- `FLT-TATE-TORSION`: `FLT.EllipticCurve.Torsion` support closure. `current_state: proved`,
  `review_state: reviewed`, `kernel_probe_state: integrated`. Axiom audit `[propext, Classical.choice,
  Quot.sound]` on `n_torsion_dimension`, `galoisRep`, `FreyCurve.torsion_rank`, `torsion_rank_two`.
  Retained AINTLIB torsion-count slice recorded under `vendor/HasseWeil` (dependency-reviewed).
- `FLT-TORSION-001`: `WeierstrassCurve.galoisRep :
  (E : WeierstrassCurve K) → (n : ℕ) → 0 < n → GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)`.
  `current_state: proved`. This is the exact object the Frey consumer feeds into `IsHardlyRamified`.
  **Regression boundary:** the design below consumes `galoisRep` and `torsion_rank` as *inputs only*;
  it adds no edge back into their proof closure.

### 2.2 The single consumer — `GaloisRepresentation.IsHardlyRamified`
`FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96-119` (structure, 4 Prop-valued fields):

- `det : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter (ℚᵃˡᵍ) ℓ g.toRingEquiv)`
- `isUnramified : ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ ℓ → ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat`
- `isFlat : ρ.IsFlatAt (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))`
- `isTameAtTwo : ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π) (δ : GaloisRep ℚ_[2] R R), ∀ g v,
   π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
   (AddSubgroup.inertia ((𝔪 Z2bar).toAddSubgroup) (Γ ℚ_[2]) ≤ δ.ker) ∧ (∀ g, δ g * δ g = 1)`

Here `ℓ = P.p` (odd exponent prime), `R = ZMod P.p`, `V = (freyCurve.map …).nTorsion P.p`, and the
`Algebra ℤ_[ℓ] (ZMod ℓ)` instance is `PadicInt.toZMod` (Frey.lean:30-31).

### 2.3 The five live `sorry` boundaries

| Obligation | Declaration (file:line) | State |
|---|---|---|
| `FLT-FREY-HR` | `FreyCurve.torsion_isHardlyRamified` — `Frey.lean:52-56` | `sorry` (assembles the 4 fields) |
| `FLT-TATE-UNRAMIFIED` | `tateCurveEquiv` (222), `tateEquiv` (339), `exists_variableChange_tateCurve` (349), `tateEquiv_baseChange` (546), `tateEquiv_galois` (561), `qUnitSepClosure`/`tateEquivSepClosure` — `TateCurve.lean`; plus `torsion_unramified_of_good_reduction` — `GoodReduction.lean:112-118` | all `sorry` |
| `FLT-TATE-FLAT` | `torsion_flat_of_good_reduction` — `Flat.lean:145-161`; `resultant_Φ_ΨSq` — `Flat.lean:244-250` | `sorry`; `resultant_Φ_ΨSq_explicit_eq_default` (224) and `isCoprime_Φ_ΨSq` (259) **proved** (latter conditional on the former) |
| `FLT-TATE-WEIL` | `WeierstrassCurve.weilPairing` — `WeilPairing.lean:38-42` | `sorry`; type admits the **zero pairing** |
| `FLT-SUPPORT-TATE` | inventory join (`kernel_probe_state: absent`) | join-only; no admission of its own |

Supporting proved leaves already available: `torsion_fixed_of_invariant_injective`
(GoodReduction.lean:60-84), `inertia_smul_residue_eq` / `inertia_residue_smul_eq` (GoodReduction.lean),
`isCoprime_Φ_ΨSq`, `resultant_Φ_ΨSq_explicit_eq_default`, and the whole proved `evalInt_*/valuation_*/
tateParameter_*/isElliptic_tateCurve/tateCurve_baseChange/qUnitSepClosure/tateQuotientGalois` block in
TateCurve.lean, plus `tatePoint`, `tatePoint_mem_torsionBy_of_mem_rootsOfUnity` and `_of_pow_eq`
(complete, but built on the `sorry`-ed `tateEquivSepClosure`).

**The nine `TateCurve.lean` admissions** (= `FLT-TATE-UNRAMIFIED` provider surface; the last belongs to
`FLT-TATE-WEIL`): `tateCurveEquiv` (224), `tateEquiv` (341), `exists_variableChange_tateCurve` (351),
`tateEquiv_baseChange` (553), `tateEquiv_galois` (566), `tateEquivSepClosure` (647),
`tatePoint_baseChange` (661), `tatePoint_galois` (668), `weilPairing_tatePoint` (717).

### 2.4 The `GaloisRep` field targets (what each consumer field dispatches to)
`FLT/Deformations/RepresentationTheory/GaloisRep.lean`:

- `IsUnramifiedAt` (316-319): `localInertiaGroup v ≤ (ρ.toLocal v).ker`.
- `IsFlatAt` (391-393): for every **open** ideal `I ⊆ A`, `(ρ.baseChange (A⧸I)).HasFlatProlongationAt v`.
- `HasFlatProlongationAt` (383-387): ∃ finite-flat Hopf algebra `G/𝒪ᵥ` with `Algebra.Etale Kᵥ (Kᵥ⊗G)`
  and a **Galois-equivariant bijection** `Additive (Kᵥ⊗G →ₐ Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.toLocal v).Space`.
  This is *exactly* the conclusion shape of `torsion_flat_of_good_reduction` (Flat.lean:145-161) —
  i.e. Flat.lean is the intended local provider; the global `IsFlatAt` is a base-change/quotient wrapper.

---

## 3. FIELD-BY-FIELD CONSUMER AND SOURCE AUDIT

### det (owner: FLT-TATE-WEIL; sources SRC-001, SRC-023)
`det ρ = ℓ-adic cyclotomic character`. Mathematically this is the statement that the Weil pairing
identifies `⋀² E[ℓ] ≅ μ_ℓ` Galois-equivariantly. Producer decomposition:
1. a **nonzero perfect alternating Galois-equivariant** pairing `E[ℓ] × E[ℓ] → μ_ℓ` (the WEIL slice);
2. `det ρ (g) = ` the scalar by which `g` acts on `μ_ℓ` = `cyclotomicCharacter … ℓ`.
Mathlib has `cyclotomicCharacter` (imported in Defs.lean) and `rootsOfUnity`; it has **no** Weil
pairing, so step 1 is the gate. Do **not** infer `det` from a zero pairing — the zero map gives
`det = 0 ≠` cyclotomic character, so the WEIL type must exclude it (see §7).

### isUnramified (owner: FLT-TATE-UNRAMIFIED; sources SRC-001, SRC-023, SRC-024)
Away from `2ℓ` the Frey curve has good reduction (discriminant `(abc)^{2p}/2^8`, Basic.lean:104), so
this is **Néron–Ogg–Shafarevich, easy direction** = `torsion_unramified_of_good_reduction`
(GoodReduction.lean). This is the *unramifiedness* path and must **not** be conflated with flatness.
Provider chain: reduction-injective-on-torsion (needs the resultant identity) →
`torsion_fixed_of_invariant_injective` (already proved) → inertia acts trivially. This slice does
**not** need the Tate curve; the Tate uniformization is for the tame-at-2 quotient, not for
unramifiedness away from `2ℓ`.

### isFlat (owner: FLT-TATE-FLAT; sources SRC-001, SRC-023, SRC-025) — **GATED**
Flat at `ℓ = P.p`. Two genuinely different cases by whether `ℓ ∣ abc`:
- `ℓ ∤ abc` (good reduction at `ℓ`, `n = ℓ = p` = residue char): needs the **finite-flat
  Hopf-algebra model at the residue characteristic** (`torsion_flat_of_good_reduction`, `n = p`).
  Division polynomials alone **cannot** produce `H` here — the `p`-torsion in the kernel of reduction
  sits at the origin, off the affine chart (Flat.lean docstring 202-214). This is Katz–Mazur 2.3.1 /
  Tate finite-flat, whose scheme vocabulary is **absent** from Mathlib.
- `ℓ ∣ abc` (multiplicative reduction at `ℓ`): flatness comes from the Tate-curve finite-flat model
  (Tate SRC-023, "Points of finite order", `0 → μ_m → E_t[m] → ℤ/mℤ → 0`), also absent from Mathlib.
**Do not** substitute unramifiedness (order invertible in residue field) for this: at `n = p` the order
is *not* invertible, so "unramified ⇒ flat" does not apply (Flat.lean docstring 77-86). This is the
single hardest field. **Second transport gap (confirmed by the FLAT consumer-slice probe):** both the
local providers (`torsion_flat_of_good_reduction`, `torsion_unramified_of_good_reduction`) act on torsion
over `AlgebraicClosure Kᵥ`/`ksep`, whereas the Frey `isFlat`/`isUnramified` fields consume the *global*
module `(freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p` through `IsFlatAt`'s
base-change-to-`A⧸I` and the absolute-Galois local restriction (`ρ.toLocal v`). **No local→global
torsion-and-inertia transport bridge exists in the pinned snapshot** — it is a distinct produced lemma,
not covered by either good-reduction theorem.

### isTameAtTwo (owner: FLT-TATE-UNRAMIFIED via the Tate curve; sources SRC-023, SRC-024)
At `2`, the Frey curve has multiplicative reduction; the Tate uniformization gives the `G_2`-stable
exact sequence `0 → K → V → W → 0` with `W` unramified and `δ² = 1`. Provider chain:
`tateEquiv`/`tateCurveEquiv` → `tateEquivSepClosure` (Galois-equivariant, base-change compatible) →
the `μ_ℓ ⊂ E_t[ℓ]` sub gives `K`, the `ℤ/ℓ` quotient gives `W`, unramified with `δ²=1` because the
quotient character is `±1`-valued (quadratic-twist ambiguity handled by SRC-024 V.5.3). The whole
`TateCurve.lean` uniformization chain is the provider; concrete local-field `X/Y` evaluation is the
open analytic core.

### 3.5 FLT-TATE-UNRAMIFIED — decomposition of the nine admissions (required analysis item 2)
Mapping the nine mathematical steps to the nine `TateCurve.lean` `sorry`s; marking mechanical-join
(probe already kernel-clean, `[propext, Classical.choice, Quot.sound]`) vs open mathematical provider:

| # | Mathematical step | Carrier decl | Class |
|---|---|---|---|
| 1 | concrete local-field evaluation of Tate `X/Y`, equation off `qℤ` | `ExplicitTateCoordinateData` → `tateCurveEquiv` | **OPEN** analytic core |
| 2 | addition law / point-map is a homomorphism | `ExplicitTatePointLawData.map_add` | **OPEN** analytic |
| 3 | char-2-safe surjectivity (retain Tate's branch) | `ExplicitTatePointLawData.surjective` | **OPEN** analytic |
| 4 | exact kernel `= qℤ` | `ExplicitTatePointMapData.ker_eq` | **JOIN** (probe: automatic from piecewise map) |
| 5 | quotient equivalence `kˣ/qℤ ≃ E_t(k)` | `tateCurveEquiv` via `QuotientAddGroup.liftEquiv` | **JOIN** (`assembleTateEquiv`) |
| 6 | local-form classification (split-mult ⇒ base-field form) | `exists_variableChange_tateCurve` (SRC-024 V.5.3) | **OPEN** source (2 local theorems; scan unchecked) |
| 7 | base change | `tateEquiv_baseChange` (up to `(ε:ℤ)•` sign) | **OPEN** (sign proof) |
| 8 | Galois compatibility | `tateEquiv_galois` (sign vanishes for `k`-linear σ) | **OPEN** (sign proof) |
| 9 | separable-closure transport | `tateEquivSepClosure` + `tatePoint_baseChange`/`_galois` | **OPEN** (consumes 6-8) |

Steps 4-5 are the only genuine mechanical joins; the analytic leaves (1-3), the local classification (6),
and the sign-controlled functoriality (7-9) are open providers. `weilPairing_tatePoint` (717) is the
tenth `sorry` and is re-owned by FLT-TATE-WEIL.

---

## 4. DEPENDENCY GRAPH AND PARALLEL SLICES

Transitively reduced. `[P]`=proved leaf, `[S]`=sorry to close, `[G]`=absent-API gate, `[J]`=join.

```
                       resultant_Φ_ΨSq [S, self-contained]   ← BEST FIRST TRANCHE
                          │ (already: resultant_Φ_ΨSq_explicit_eq_default [P], isCoprime_Φ_ΨSq [P])
        ┌─────────────────┴───────────────────┐
        ▼                                      ▼
 reduction-injective-on-torsion [S]     good-reduction étale prolongation, n coprime to p [S]
        │  (+ torsion_fixed_of_invariant_injective [P])   │
        ▼                                      ▼
 torsion_unramified_of_good_reduction [S] ── (isFlat, n∤p case reduces to unramified) ──┐
        │  → FIELD isUnramified                                                          │
        │                                     finite-flat Hopf model @ p  [G] ───────────┤ → FIELD isFlat
        │                                     (Katz–Mazur/Tate; NO Mathlib leaf)         │
        ▼                                                                                ▼
 concrete Tate X/Y eval [S] → tateCurveEquiv [S] → tateEquiv [S] → tateEquiv_baseChange/galois [S]
        │                          (+ exists_variableChange_tateCurve [S] via SRC-024 V.5.3)
        ▼
 tateEquivSepClosure [S] ──┬──► FIELD isTameAtTwo  (K/W exact seq, δ²=1)
                           └──► weilPairing nonzero/perfect/alt/equivariant [G] → Tate normalization
                                     → FIELD det  (⋀²E[ℓ] ≅ μ_ℓ ⇒ det = cyclotomicCharacter)
                                     (NO Mathlib Weil-pairing leaf)

 galoisRep [P, FLT-TORSION-001] ─┐
 torsion_rank [P, FLT-TATE-TORSION]├─► FreyCurve.torsion_isHardlyRamified [S]  (FLT-FREY-HR)
 {det, isUnramified, isFlat, isTameAtTwo} ─┘        ▲
                                                    │
                        FLT-SUPPORT-TATE [J] = inventory join over the four support subclusters
```

**Independent parallel slices** (no cross-edge until the join): (A) UNRAMIFIED-away-from-2ℓ =
{resultant, reduction-injectivity, good-reduction unramified}; (B) FLAT@p Hopf model [G]; (C) TATE
uniformization → tameAtTwo; (D) WEIL pairing [G] → det. Slice A feeds the `n∤p` part of C-adjacent
flat; B and D are the two gates. The join `FLT-SUPPORT-TATE` waits for all four subclusters and adds
no admission of its own; `FLT-FREY-HR` then assembles the four fields onto `galoisRep`.

Regression edges (inbound only, never reopened): `galoisRep [FLT-TORSION-001]` and
`torsion_rank [FLT-TATE-TORSION]` → `torsion_isHardlyRamified`.

---

## 5. PROPOSED LEAN SIGNATURES (dependency order)

Legend: `E`=existing, `P`=probe-proved-conditional, `N`=new produced lemma, `G`=source gate.

```lean
-- [E, already proved] degree-normalization of the resultant
theorem WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default {R₀} [CommRing R₀]
  (W : WeierstrassCurve R₀) (n : ℤ) : … -- Flat.lean:224

-- [N] BEST FIRST TRANCHE — universal division-polynomial resultant identity
theorem WeierstrassCurve.resultant_Φ_ΨSq {R₀} [CommRing R₀] (W : WeierstrassCurve R₀)
  {n : ℤ} (hn : n ≠ 0) :
  (W.Φ n).resultant (W.ΨSq n) (n.natAbs^2) (n.natAbs^2 - 1) = W.Δ ^ ((n.natAbs^4 - n.natAbs^2)/6)
  ∨ … = -W.Δ ^ (…)   -- Flat.lean:244; unblocks isCoprime_Φ_ΨSq [already proved conditional on this]

-- [N] reduction is injective on n-torsion when Δ is a unit (from isCoprime_Φ_ΨSq) → then:
-- [S→N] the good-reduction unramifiedness provider (fills the current sorry)
theorem WeierstrassCurve.torsion_unramified_of_good_reduction … :
  ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n:ℤ),
    Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P   -- GoodReduction.lean:112

-- [G] finite-flat Hopf model (fills the current sorry; NO Mathlib leaf for the n=p case)
theorem WeierstrassCurve.torsion_flat_of_good_reduction … :
  ∃ (H) (_:CommRing H)(_:HopfAlgebra R H)(_:Module.Finite R H)(_:Module.Flat R H)
    (_:Algebra.Etale K (K ⊗[R] H)) (f : Additive (WithConv (K⊗[R]H →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (n:ℤ)), <Galois-equivariance>   -- Flat.lean:145

-- [P, migrate] concrete Tate coordinate/point-map → equiv (probes already kernel-clean)
--   ExplicitTateCoordinateData / ExplicitTatePointLawData / ExplicitTatePointMapData
--   → WeierstrassCurve.tateCurveEquiv (TateCurve.lean:222)  [analytic X/Y eval = open core]
theorem WeierstrassCurve.exists_variableChange_tateCurve … -- TateCurve.lean:349, via SRC-024 V.5.3
noncomputable def WeierstrassCurve.tateEquiv … -- TateCurve.lean:339
theorem WeierstrassCurve.tateEquiv_baseChange … / tateEquiv_galois … -- 546 / 561 (sign-controlled)
-- → tateEquivSepClosure (Galois-equivariant separable-closure transport)

-- [G] WEIL: REFINE the type so the zero map is excluded (this refinement is a kernel-clean
--     signature tranche even though the construction is gated). Proposed bundled structure:
structure WeierstrassCurve.WeilPairingData (k) [Field k] [IsSepClosed k] [DecidableEq k]
    (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) [NeZero (n:k)] where
  pair   : torsionBy (E⁄k).Point (n:ℤ) →+ torsionBy (E⁄k).Point (n:ℤ) →+ Additive (rootsOfUnity n k)
  alt    : ∀ P, pair P P = 0
  perfect: ∀ P, P ≠ 0 → ∃ Q, pair P Q ≠ 0          -- excludes the zero inhabitant
  equiv  : ∀ (σ : k ≃ₐ[k] k) P Q, pair (σ • P) (σ • Q) = σ • pair P Q   -- Galois-equivariance
-- and the Tate normalization theorem tying `pair` on E_t[ℓ] to the μ_ℓ ⊂ E_t[ℓ] sub of SRC-023.

-- [S] final assembly onto the frozen consumer, on galoisRep (regression input)
theorem FreyCurve.torsion_isHardlyRamified (P : FreyPackage) :
  IsHardlyRamified P.hp_odd (FreyCurve.torsion_rank P)
    (P.freyCurve.galoisRep P.p P.hppos) -- Frey.lean:52
```

---

## 6. LIBRARY MATCHES  *(confirmed by the library-verification sweep)*

**FOUND (usable leaves):**
- `cyclotomicCharacter` / `modularCyclotomicCharacter : (L ≃+* L) →* (ZMod n)ˣ`
  (`Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter`, imported in Defs.lean).
- `ZMod.unitsMap (h : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ` (`Mathlib/Data/ZMod/Units.lean:25`).
- `rootsOfUnity` (`Mathlib/RingTheory/RootsOfUnity/`), `Subgroup.zpowers`, multiplicative quotient.
- Division polynomials `Φ`, `ΨSq`, `natDegree_Φ`, `natDegree_ΨSq_le`, `leadingCoeff_ΨSq`,
  `Polynomial.resultant`, `exists_mul_add_mul_eq_C_resultant`, `resultant_add_right_deg` — **FOUND**.
- `WeierstrassCurve.HasGoodReduction`, `ValuationSubring.inertiaSubgroup`
  (`Mathlib/RingTheory/Valuation/RamificationGroup.lean:50`), `AddSubgroup.inertia`, `Affine.Point.map`,
  `torsionBy` — **FOUND**.
- `HopfAlgebra` (`Mathlib/RingTheory/HopfAlgebra/Basic.lean:68`), `Bialgebra.Convolution`,
  `Algebra.Etale`, `Module.Flat`, `Module.Finite` — **FOUND (raw typeclasses only)**.
- `GaloisRep.det` — **FOUND in FLT's own layer** (used at Defs.lean:107; `FramedGaloisRep.det_baseChange`
  at GaloisRep.lean:297). So the `det` *field target* is expressible; what is missing is the theorem
  equating it to `cyclotomicCharacter`, which needs the Weil pairing.

**NONE FOUND (the gates — do not infer from terminology):**
- Weil pairing `e_n`, Miller functions, elliptic divisors / Picard group — **NONE FOUND** in Mathlib.
  (`vendor/HasseWeil/.../WeilPairing/` holds torsion-*cardinality* theorems named "WeilPairing", not a
  pairing map.) FLT's `weilPairing` (WeilPairing.lean:38) is a `sorry` whose type admits the zero map.
- `E[n]`-as-group-scheme, `FiniteFlatGroupScheme`, Cartier dual, Katz–Mazur "×n finite locally free",
  affine-group-scheme-represents-finite-group (Tannakian) — **NONE FOUND**. Only the ingredient
  typeclasses exist, which is exactly why `torsion_flat_of_good_reduction` can be *stated* but not proved.
- Tate curve / uniformization / q-expansion / rigid-analytic torus — **NONE FOUND** in Mathlib; the
  repo's own `TateCurve*.lean` are the only carriers, `sorry` at every analytic/functorial leaf.
- Dedicated determinant-of-Galois-representation *functor* in Mathlib — **NONE FOUND** (FLT supplies its
  own `GaloisRep.det`; see FOUND list).
- Packaged local-inertia-fixedness ⇒ global-module transport across base change to `ksep` — **NONE FOUND**
  (the FLAT second-transport-gap of §3).

---

## 7. COUNTEREXAMPLES AND FAILURE MODES

1. **Zero pairing.** `weilPairing := sorry` (WeilPairing.lean:42); its type
   `torsionBy → torsionBy → Additive (rootsOfUnity)` is inhabited by `0`. The permanent regression
   `FLTMethodology/Probes/WeilPairingBoundary.lean` makes this explicit: `zeroPairing := 0` typechecks,
   and `zeroPairing_ne_nontrivial_value` (proved) shows it cannot satisfy the frozen normalization
   `weilPairing_tatePoint` (TateCurve.lean:711-717) at a nontrivial `ζ`. Filling `weilPairing` with `0`
   would typecheck but be mathematically false at its consumer, and `det` would collapse to `0 ≠`
   cyclotomic. **Fix:** the `WeilPairingData` bundle in §5 adds `perfect` (and `alt`, `equiv`), which the
   zero map fails; any WEIL provider lacking these is rejected. Note `weilPairing_tatePoint` consumes the
   `sorry`-ed `tateEquivSepClosure`, so WEIL cannot be audited independently of FLT-TATE-UNRAMIFIED.
2. **Same `j`, nontrivial quadratic twist.** Equal non-integral `j` gives only a form over the base
   field; only *split* multiplicative reduction selects the untwisted Tate form (SRC-024 V.5.3).
   `exists_variableChange_tateCurve` must consume split-multiplicative-reduction, not just `j`.
3. **Characteristic-two division.** Tate surjectivity has a genuine char-2 branch
   (SRC-023 Thm 1, book pp.169-173); no step in `tateCurveEquiv`/tameAtTwo may divide by 2.
4. **Quotient without exact kernel + surjectivity.** A homomorphism from `kˣ/qℤ` is not an `AddEquiv`;
   both `ker_eq = qℤ` and `Surjective` are required (`ExplicitTatePointMapData`).
5. **Unramified-used-as-flat at residue char.** "order invertible ⇒ unramified ⇒ flat" is valid only
   for `n ∤ p`; at `n = p` it is false. The `isFlat` field must not be discharged via
   `torsion_unramified_of_good_reduction`.
6. **Algebraic vs separable closure.** Torsion/Weil live over `ksep`/`IsSepClosed`; `galoisRep` uses
   `AlgebraicClosure ℚ`. Transport must go through `tateEquivSepClosure`, not silently swap closures.
7. **Sign / functoriality mismatch.** `tateEquiv` for a general `E` carries a `±1` from the choice of
   variable change; `tateEquiv_baseChange` is only correct up to `(ε:ℤ)•` (TateCurve.lean:546). Keep
   on-the-nose naturality of the *explicit* map separate from the general-curve sign.
8. **Wrong base-change of a local action.** `isTameAtTwo` transports the `Γ ℚ_[2]`-action through
   `algebraMap ℚ ℚ_[2]`; using the wrong embedding breaks equivariance. `IsUnramifiedAt` fixes an
   arbitrary valuation on `Kᵃˡᵍ` (GaloisRep.lean:307) — must be threaded consistently.
9. **Circularity.** No slice may consume `torsion_isHardlyRamified` (or any of its four fields'
   downstream) — the graph is a DAG rooted at the four independent field providers.

---

## 8. FIRST BUILDABLE SLICES

**Best first tranche overall — `WeierstrassCurve.resultant_Φ_ΨSq` (Flat.lean:244).**
- *Placement/imports:* already in `FLT/KnownIn1980s/EllipticCurves/Flat.lean` (division-polynomial,
  resultant imports present).
- *Existing inputs:* `resultant_Φ_ΨSq_explicit_eq_default` [P], `coeff_Φ`, `natDegree_Φ`,
  `natDegree_ΨSq_le`, `leadingCoeff_ΨSq`; base-change stability of resultants.
- *Why first:* purely polynomial, self-contained, **no absent API**, base-change stable, and it is the
  sole remaining input to `isCoprime_Φ_ΨSq` (already proved conditional on it), which in turn unblocks
  reduction-injectivity → the whole UNRAMIFIED slice A and the `n∤p` flat case.
- *Expected first residual goal:* prove `Res(Φ n, ΨSq n) = ±Δ^((n⁴−n²)/6)` over the universal
  `ℤ[a₁..a₆]` (where `Δ` is irreducible ⇒ resultant `= ±c·Δ^k`), pin `c=±1` by reducing mod every `ℓ`,
  pin `k=(n⁴−n²)/6` by weight/isobaric count; then base-change to arbitrary `R₀`.
- *Audit:* `#print axioms WeierstrassCurve.resultant_Φ_ΨSq` (expect `[propext, Classical.choice,
  Quot.sound]`).

Per-slice first tranches:
- **UNRAMIFIED:** resultant → reduction-injectivity → fill `torsion_unramified_of_good_reduction`
  (GoodReduction.lean:112) using the proved `torsion_fixed_of_invariant_injective`. Audit that decl.
- **FLAT:** the `n∤p` étale-prolongation half of `torsion_flat_of_good_reduction`, reducing to the
  unramified module (Flat.lean docstring 190-201). The `n=p` half is the gate — leave a precisely
  documented `sorry` with the Katz–Mazur/Tate locator, do **not** fake it.
- **TATE:** migrate the kernel-clean probes `TateCoordinatePointMapBoundaryProbe.tateCurveEquivOfCoordinates`
  and `TateUniformizationAssemblyProbe.assembleTateEquiv` into the repo as the mechanical scaffold;
  first genuine residual = concrete local-field `X/Y` evaluation + equation off `qℤ`.
- **WEIL:** land the `WeilPairingData` structure (signature tranche, kernel-clean, excludes zero map);
  construction stays gated.

---

## 9. STOP-LOSS GATES

- **False statement:** none detected in `IsHardlyRamified` or the provider signatures. Trip if any
  provider is restated to make it provable (e.g. dropping `perfect` from WEIL, or `isFlat` weakened to
  unramified at `p`).
- **Unverified printed source scope:** SRC-024 (Silverman V.5.3) book scan **not yet visually checked**
  — must inspect field/completeness/discreteness/residue-char hypotheses before authorizing
  `exists_variableChange_tateCurve` across the repo's full `IsNonarchimedeanLocalField` scope. SRC-023
  Tate Thm 1 char-2 branch is checked.
- **Absent foundational API (TRIPPED, bounded):** finite-flat group-scheme/Cartier-duality model at the
  residue characteristic (FLAT@p) and the Weil-pairing/Miller/divisor machinery (WEIL) — **NONE FOUND**
  in Mathlib. These block *closure* of two fields but not the design; escalate to the reviewer for a
  build-vs-named-assumption decision.
- **Unapproved named assumption:** none introduced. If FLAT@p or WEIL cannot be built at T1, any
  substitute must be a *named source gate* tied to an approved SRC entry, decided by review — not an
  ad-hoc axiom.

---

## 10. DEFINITION OF READY (per obligation + join)

- **FLT-TATE-UNRAMIFIED — DoR: NEAR.** Signatures exact and elaborating; `resultant_Φ_ΨSq` + reduction
  injectivity are the only blockers for the good-reduction (away-from-`2ℓ`) core; Tate uniformization
  chain has exact signatures but open analytic core + unchecked SRC-024 scope. Ready to start slice A.
- **FLT-TATE-FLAT — DoR: PARTIAL/GATED.** `n∤p` case ready via slice A; `n=p` case needs absent API.
  Ready to start the reduction half; the gate must be flagged, not filled.
- **FLT-TATE-WEIL — DoR: PARTIAL/GATED.** `WeilPairingData` refinement ready now; construction gated.
- **FLT-FREY-HR — DoR: BLOCKED-ON-FIELDS.** Assembly is mechanical once the four fields exist; nothing
  to build until then except wiring `det` to `cyclotomicCharacter` via the WEIL normalization.
- **FLT-SUPPORT-TATE (join) — DoR: NOT READY.** Inventory join; `kernel_probe_state: absent`. Must be
  decomposed into its four subcluster declaration nodes (done above) before its wave; introduces no
  admission of its own.

---

## 11. OPEN QUESTIONS FOR SYNTHESIS / GPT REVIEW

1. **Build vs named gate for FLAT@p and WEIL.** T1 policy decision: build the finite-flat-scheme and
   Weil-pairing theories, or carry each as a named source gate (SRC-023/025) with a declared axiom
   boundary? This is the load-bearing routing choice.
2. **SRC-024 scope audit.** Authorize a read-only visual check of Silverman V.5.3's printed hypotheses
   before `exists_variableChange_tateCurve` is built at full local-field generality.
3. **Does `isFlat` at `ℓ ∣ abc` route through the Tate finite-flat model or a separate multiplicative-
   reduction flatness lemma?** Confirm the Frey `isFlat` field genuinely needs the `n=p` Hopf model in
   *both* reduction cases, or whether the good-reduction (`ℓ∤abc`) case suffices for the actual Frey
   package constraints.
4. **`Algebra.Etale` redundancy.** GaloisRep.lean:377-381 notes the étale condition is redundant in
   char 0 but hard to prove generally; confirm the intended discharge for `HasFlatProlongationAt`.
5. **Library NONE-FOUND set confirmed** (Weil pairing, finite-flat group scheme as an object, Tate
   uniformization, packaged local→global torsion transport). §6 is final. `GaloisRep.det` exists; the
   `det` field is a theorem gap (tie to cyclotomic character via Weil), not an API gap.
6. **`FreyPackage.mazur` (FLT-HIST-MAZUR)** is a *separate* named-axiom obligation feeding
   `torsion_not_isIrreducible` (Frey.lean:58, also `sorry`); it is **out of this cluster's scope** but
   shares the file. Confirm the reviewer does not expect `torsion_not_isIrreducible` from this lane.

---

*Prepared read-only. Contains no edits to the repository; the only file written is this plan. All seven
control rows, both proved regressions, the four consumer fields, the ten `TateCurve.lean` admissions,
and the Mathlib NONE-FOUND set are verified against source and quoted above.*
