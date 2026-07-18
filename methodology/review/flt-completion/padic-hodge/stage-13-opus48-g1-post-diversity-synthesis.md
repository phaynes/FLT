# Opus 4.8 post-diversity synthesis — p-adic-Hodge G1 period-functor infrastructure

**VERDICT: `READY-FOR-GPT-REVIEW`**

Task `task:fg-flt-ra-math-source-design-20260716`, obligation `FLT-MLT-PADIC-HODGE`, node **G1**.
Read-only synthesis reconciling stage-9 (Opus, `DECOMPOSE-FIRST`), stage-11 (GPT-5.6 xhigh,
`REVISE-SUBSTANTIVE`), stage-12 (Fable-5, `DESIGN-VIABLE`). This document authorizes **no** production
build, graph mutation, `IsCrystallineAt` theorem, comparison theorem, T2 assumption, or obligation
promotion. An independent GPT review of the exact bankable slice below remains mandatory (the recorded
`next_gate`).

---

## Context — why this synthesis exists

The Tier-1 weight/dual probe (`FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`, namespace
`FLTMethodology.Taylor2018`) is coefficient-independent and carries **no** crystalline field by design
(documented Tier-2 gap). G1 is the first genuine provider beneath it: an exact crystalline predicate
backed by a real period ring. All three stages agree a genuine `B_cris`/`D_cris` **cannot** be defined
against the pin. The deliverable is the *smallest honest slice that can bank now* plus an exact, ordered
provider graph for everything deferred. Stage-9 proposed the slice but with two defects; stage-11
enumerated six repairs; stage-12 repaired and probed them. This synthesis confirms the reconciliation
by independent read-only verification of every cited API and fixes the residual stage-9 defect.

---

## Pin and source verification (independently re-confirmed, read-only)

Working tree `5c717f1` = `c6c1a7d` + only the stage-13 prompt file (verified via `git diff`); all source
docs and the probe are byte-identical to `c6c1a7d`, so reading the tree is source-faithful.

- `lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`; `.lake/packages/mathlib` HEAD =
  `a3364faec42918fcd84a03a255b50570129f9ead` (matches the pin).
- **`FixedPoints.subring` — argument order confirmed.** `Mathlib/Algebra/Algebra/Subalgebra/
  Operations.lean:98` : `def FixedPoints.subring : Subring B` under
  `variable (A B B' …) (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]`, i.e.
  **`FixedPoints.subring B G`** (module first, group second). Line 102 supplies
  `instance : SMulCommClass G (FixedPoints.subring B G) B`. ⇒ **stage-12's `FixedPoints.subring B Γ`
  is correct; stage-9 §4b's `FixedPoints.subring Γ B` is a WRONG argument order and is retracted.**
- **`DistribMulAction.toLinearEquiv`** `Mathlib/Algebra/Module/Equiv/Basic.lean:194`, under
  `variable (R M) [Semiring R] [AddCommMonoid M] [Module R M] [Group S] [DistribMulAction S M]
  [SMulCommClass S R M]`. ⇒ stage-12's required block `[Group Γ] [DistribMulAction Γ B]
  [SMulCommClass Γ E B]` (with `MulSemiringAction Γ B → DistribMulAction Γ B`) is exact.
- **`TensorProduct.congr`** `Mathlib/LinearAlgebra/TensorProduct/Map.lean:248` — exists.
- **`ℂ_[ℓ]` field exists, action absent.** `Mathlib/NumberTheory/Padics/Complex.lean`:
  `abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]` (line 54), `PadicComplex p`/`ℂ_[p]` (completion),
  `PadicComplexInt`/`𝓞_ℂ_[p]`. Grep of that file for `MulSemiringAction`/`≃ₐ[` — none.
- **`DividedPowers/` = {Basic, DPMorphism, Padic, RatAlgebra, SubDPIdeal}** — no envelope, no
  universal property (grep `envelope` empty). ⇒ N-PD genuinely absent.
- **`A_cris` / `B_cris` / `D_cris` / `IsCrystalline` — grep of all of Mathlib is EMPTY.** Confirmed
  absent at pin.
- **BDeRham `ker θ` principality open.** `Mathlib/RingTheory/Perfectoid/BDeRham.lean` TODO 3 verbatim:
  "Show that ker θ is principal when the base ring is integral perfectoid." `fontaineTheta`
  (`Perfectoid/FontaineTheta.lean:165`) exists.
- **FLT anchors:** `GaloisRep` (`FLT/Deformations/RepresentationTheory/GaloisRep.lean:49`),
  notation `Γ K = Field.absoluteGaloisGroup K` (line 38), `GaloisRep.map` via
  `Field.absoluteGaloisGroup.map`. `HeightOneSpectrum.asIdeal`/`adicCompletion` present.
- **Control rows** (`methodology/control/proof-obligations.ndjson`, `proof-graph.ndjson`,
  `source-design.ndjson`): `FLT-MLT-PADIC-HODGE` `review_state =
  tier1-reviewed-g1-fable-repair-complete-opus-synthesis-ready`, `kernel_probe_state =
  tier1-boundary-green-g1-candidates-external-probe-green`, `dor =
  TIER1-REVIEWED-G1-POST-DIVERSITY-SYNTHESIS-RUNNING`, `next_gate = "Complete Opus synthesis …, then
  GPT independently reviews the exact bankable slice. No IsCrystallineAt theorem or full promotion is
  authorized."` Consumers: `FLT-MLT-SOURCE`, `FLT-SGOOD-SELECTED`, `FLT-RACAR-DEF`.

---

## 1. Smallest bankable period-functor slice (exact)

**File:** `FLTMethodology/Probes/MLTPadicHodgePeriodFunctor.lean` (new probe; sibling of the Tier-1
probe). **Namespace:** `FLTMethodology.Taylor2018`. **Universes:** fully polymorphic — every carrier is
`Type*`; no universe constraint (matches the Tier-1 probe style; `K : Type*` suffices here since only
`HeightOneSpectrum (𝓞 K)` is used, not the universe-explicit `GaloisRep`). **Dependency:** mathlib-only
(no FLT import needed — the tensor block uses an *abstract* `Γ : Type* [Group Γ]`, not the FLT `Γ K`).

Precise imports:
```
import Mathlib.RingTheory.DedekindDomain.Ideal            -- HeightOneSpectrum, asIdeal
import Mathlib.NumberTheory.NumberField.Basic             -- NumberField, 𝓞 K, CharZero (𝓞 K)
import Mathlib.NumberTheory.Padics.PadicNumbers           -- ℚ_[ℓ]
import Mathlib.Algebra.Ring.Action.Basic                  -- MulSemiringAction
import Mathlib.Algebra.Algebra.Subalgebra.Operations      -- FixedPoints.subring (B G) + SMulCommClass inst
import Mathlib.Algebra.Module.Equiv.Basic                 -- DistribMulAction.toLinearEquiv
import Mathlib.LinearAlgebra.TensorProduct.Map            -- TensorProduct.congr
import Mathlib.LinearAlgebra.Dimension.Finrank            -- Module.finrank
```

### Block A — guarded place predicate (probe P1)
```lean
open IsDedekindDomain NumberField

-- counterexample guard: the unguarded ℓ:ℕ predicate is vacuous at ℓ = 0 (documents why [Fact ℓ.Prime])
theorem unguarded_natCast_mem_of_zero
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ((0 : ℕ) : 𝓞 K) ∈ v.asIdeal := by simpa using v.asIdeal.zero_mem

/-- `v` lies above the rational prime `ℓ`. Guarded by `[Fact ℓ.Prime]` (Tier-1 `ℚ_[ℓ]` convention). -/
def IsPlaceAbove (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (ℓ : 𝓞 K) ∈ v.asIdeal
```
plus non-vacuity on all three axes (stage-12 P1, trio-clean):
- `IsPlaceAbove.natCast_ne_zero` (nonzero witness in a proper ideal; `CharZero (𝓞 K)` synthesizes),
- `IsPlaceAbove.unique` (a place lies above at most one prime; coprimality of distinct primes),
- `exists_prime_natCast_mem` (every place lies above **some** prime; via `Ideal.absNorm`, comap
  primality, PID generator).

### Block B — explicit diagonal tensor representation (probe P2)
```lean
variable (Γ : Type*) [Group Γ]
variable (E : Type*) [CommRing E]
variable (B : Type*) [CommRing B] [Algebra E B] [MulSemiringAction Γ B] [SMulCommClass Γ E B]
variable (V : Type*) [AddCommGroup V] [Module E V] [DistribMulAction Γ V] [SMulCommClass Γ E V]

noncomputable def diagTensorAut (g : Γ) : (B ⊗[E] V) ≃ₗ[E] (B ⊗[E] V) :=
  TensorProduct.congr (DistribMulAction.toLinearEquiv E B g) (DistribMulAction.toLinearEquiv E V g)

@[simp] theorem diagTensorAut_tmul (g : Γ) (b : B) (x : V) :
    diagTensorAut Γ E B V g (b ⊗ₜ[E] x) = (g • b) ⊗ₜ[E] (g • x) := rfl

noncomputable def diagTensorRep : Γ →* ((B ⊗[E] V) ≃ₗ[E] (B ⊗[E] V))   -- map_one'/map_mul' proved

-- semilinearity of the action w.r.t. left-factor scaling (TensorProduct.induction; smul_tmul' + smul_mul')
theorem diagTensorAut_smul_left (g : Γ) (b : B) (x : B ⊗[E] V) :
    diagTensorAut Γ E B V g (b • x) = (g • b) • diagTensorAut Γ E B V g x
```
Both `SMulCommClass Γ E B` and `SMulCommClass Γ E V` are **required** — they are exactly the `E`-linearity
of each factor action consumed by `DistribMulAction.toLinearEquiv` (verified above).

### Block C — invariant submodule with explicit scalar closure (probe P2/P0/P0c)
```lean
noncomputable def periodSubmodule : Submodule (FixedPoints.subring B Γ) (B ⊗[E] V) where
  carrier := {x | ∀ g : Γ, diagTensorAut Γ E B V g x = x}
  zero_mem' g := map_zero _
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  smul_mem' := by                       -- EXPLICIT closure; ⟨b,hb⟩ • x, hb : ∀ g, g • b = b
    rintro ⟨b, hb⟩ x hx g
    show diagTensorAut Γ E B V g (b • x) = b • x
    rw [diagTensorAut_smul_left, hb g, hx g]

theorem mem_periodSubmodule ... := Iff.rfl
theorem periodSubmodule_eq_top ... -- trivial action ⇒ invariants are everything (sanity)
```
Scalar closure is a **hand proof**: stage-12 P0c confirms `SMulCommClass Γ (FixedPoints.subring B Γ)
(B ⊗[E] V)` is not merely unsynthesized but *unstatable* (its `SMul Γ (B ⊗[E] V)` argument has no
instance) — consistent with the diamond rejection below.

### Block D — Qp-relative dimension predicate (probe P2) — **banked with mandatory honest docstring**
```lean
/-- Dimension coincidence for the invariants of `B ⊗[ℚ_[ℓ]] V` over the fixed subring `Bᴳ`,
    RELATIVE to a supplied `Γ`-`B`. This is the crystalline predicate ONLY when `B := B_cris`
    (deferred provider N3–N7); for a general `B` it is a bare finrank equality and asserts NOTHING
    about crystallinity, `D_cris`, Hodge–Tate weights, or the `≤` comparison. Not `IsCrystallineAt`;
    not a comparison theorem. -/
def IsCrystallineRelQp
    (Γ : Type*) [Group Γ] (ℓ : ℕ) [Fact ℓ.Prime]
    (B : Type*) [CommRing B] [Algebra ℚ_[ℓ] B] [MulSemiringAction Γ B] [SMulCommClass Γ ℚ_[ℓ] B]
    (V : Type*) [AddCommGroup V] [Module ℚ_[ℓ] V] [Module.Finite ℚ_[ℓ] V]
      [DistribMulAction Γ V] [SMulCommClass Γ ℚ_[ℓ] V] : Prop :=
  Module.finrank (FixedPoints.subring B Γ) (periodSubmodule Γ ℚ_[ℓ] B V)
    = Module.finrank ℚ_[ℓ] V
```

**Dependency order inside the slice:** A (independent) → B → C → D. Blocks B–D reuse the same variable
block; D pins `E := ℚ_[ℓ]` and keeps the fixed scalars the abstract `FixedPoints.subring B Γ` (never
named `K₀`). Persisted declaration count ≈ 13 (5 + 4 + 3 + 1); stage-12's "12" excluded the guard or a
`@[simp]` lemma — a bookkeeping note only, immaterial to the axiom gate which covers **all persisted
declarations**.

---

## 2. Re-probe conclusions and the two rejections

- `IsPlaceAbove` guarded, non-vacuity/uniqueness/existence: **verified** by reading each cited pinned
  lemma; stage-12 P1 compiled them trio-clean. The `ℓ = 0` counterexample is real (guard retained).
- diagonal action / semilinearity / invariant submodule / `IsCrystallineRelQp`: signatures type-check
  against the exact instance blocks I re-verified above.
- **REJECT any global/scoped `SMul Γ (B ⊗[E] V)` instance.** Stage-12 P0b shows it does not synthesize
  under this hypothesis order; mathlib's `TensorProduct.leftHasSMul` needs `SMulCommClass E Γ B` and
  `SMulCommClass.symm` is a *local* instance (`LinearAlgebra/TensorProduct/Basic.lean:338`). A symmetric
  `SMulCommClass` context would then collide and silently act on the **left factor only** (action
  diamond). The Γ-action therefore lives **only** in `diagTensorAut`/`diagTensorRep`; the slice never
  writes `g • x` on `B ⊗[E] V`. If a later node needs the action as an instance, it must use a **type
  synonym**, never a bare instance on `B ⊗[E] V`.

---

## 3. Decision on `IsCrystallineRelQp`

**Safe to bank as relative vocabulary** — kept in the slice — **conditioned on the mandatory docstring
above**. Rationale: it is (a) explicitly *relative* to a supplied `B` (the `Rel` qualifier is load-
bearing), (b) pinned to `E = ℚ_[ℓ]` so it dodges the ramified-`E` fallacy stage-11 flagged, (c) a plain
`finrank` equality that claims neither the always-true `≤` direction nor crystallinity, and (d)
explicitly **not** `IsCrystallineAt` and **not** a comparison theorem. It is the honest "expose the
mathematics, do not hide a theorem in a `Prop`" answer to the hostile check.

**Flag for GPT review (one open naming decision):** the token `Crystalline` in the name remains mildly
suggestive for an arbitrary `B`. Acceptable options for the reviewer: (i) keep `IsCrystallineRelQp`
with the honest docstring (my recommendation — the `Rel`/`Qp` qualifiers + docstring make relativity
unmissable); or (ii) rename to a neutral `periodRankMatchesQp` / `IsPeriodRegularRelQp`, reserving
`Crystalline` for the `B := B_cris` instantiation. This is the single point where reasonable reviewers
may differ; no mathematical content changes either way.

---

## 4. Exact new provider nodes (proposed for later review — NOT built here)

### N-Cp [P] — continuous Galois action on `ℂ_[ℓ]`, d=7
- **Target:** a continuous `MulSemiringAction (Γ ℚ_[ℓ]) ℂ_[ℓ]` extending the `AlgEquiv` action on
  `PadicAlgCl ℓ` by isometry, plus the `Γ Kᵥ ↪ Γ ℚ_[ℓ]` indexing via `Field.absoluteGaloisGroup.map`.
- **Deps:** `PadicComplex`/`PadicAlgCl` (present at pin), uniqueness of the spectral-norm extension
  (`spectralNorm`), `UniformSpace.Completion.map`/`mapRingHom`, `ContinuousSMul`, FLT
  `AbsoluteGaloisGroup.map`. The **field exists; only the action is absent** (correcting stage-9's
  "closure omits `C_p`").
- **Owner:** FLT methodology; upstream-candidate to mathlib.
- **Completion gate:** the `MulSemiringAction (Γ ℚ_[ℓ]) ℂ_[ℓ]` + `ContinuousSMul` instances elaborate,
  each σ proven norm-preserving, standard-trio clean.
- **First residual Lean goal:** `∀ σ : PadicAlgCl ℓ ≃ₐ[ℚ_[ℓ]] PadicAlgCl ℓ, Isometry σ` from
  uniqueness of the spectral-norm extension.

### N-PD [P] — PD-envelope of an ideal, d=8
- **Target:** the divided-power envelope of a ring along an ideal, with its universal property
  (required by N3: `A_cris` = p-completed PD-envelope of `W(𝒪_{C♭})` along `ker θ`).
- **Deps:** `RingTheory/DividedPowers/{Basic, SubDPIdeal, DPMorphism}`. **Absent at pin** (no
  `envelope` in the directory).
- **Owner:** FLT methodology, tracking any upstream divided-power-envelope PR; adopt only on
  exact-declaration match at a new pin.
- **Completion gate:** envelope construction + universal property elaborate, trio-clean.
- **First residual Lean goal:** state the universal property (initial PD-algebra under a ring with the
  ideal PD-extended) as a `def` + characterizing `theorem`; nothing to reuse at the pin.

### Deferred provider graph (proposed rows/edges for GPT review, not mutated)
```
slice (Blocks A–D)                              LANDED-READY (probe-audited; re-run at build)
  → N-Cp [P] continuous Γ-action on ℂ_[ℓ]        d=7   (field exists; action absent)
  → N-PD [P] PD-envelope of an ideal             d=8   (absent at pin)
  → N3   [P] A_cris = p-completed PD-env of W(𝒪_{C♭}) along ker θ   d=9   (needs N-Cp, N-PD, ξ-princ.)
  → N4   [P] Frobenius φ on A_cris               d=8
  → N5a  [P] ξ generates ker θ                   d=7   (mathlib BDeRham TODO 3)
  → N5b  [P] t = log[ε] ∈ A_cris, χ_cyc-eigenvector; t ~ ξ up to unit in B_dR⁺   d=8
  → N6   [P] B_cris = A_cris[1/t], continuous Γ Kᵥ-action           d=8
  → N7   [P] B_cris^{Γ} = K₀ (theorem provider — NEVER a field)     d=9
  → N-E  [P] finite coefficients: D as a K₀ ⊗[ℚ_[ℓ]] E module       d=7
  → N9   [I] assembly: IsCrystallineAt := IsCrystallineRelQp at B := B_cris   d=4   (BLOCKED until N3–N7)
```
Each of N3–N7 is a **separate** provider with its own review; they must not be estimated as one task.

---

## 5. `ξ`, `t`, and `K₀` — corrected roles (retracting stage-9)

- **`ξ` generates `ker θ`.** `ξ = [p^♭] − p ∈ A_inf = W(𝒪_{C♭})` generates `ker(fontaineTheta)`; its
  principality is precisely BDeRham TODO 3 and the input N-PD/N3 need. **Stage-9's "t = generator of
  ker θ" is wrong and is retracted** (confirmed against BDeRham.lean).
- **`t = log [ε]`** converges only in `A_cris`, satisfies `θ t = 0`, `g • t = χ_cyc(g) · t`; it
  generates `Fil¹ B_dR⁺` (a theorem comparing `t` to `ξ` up to a unit, downstream of ξ-principality and
  the B_dR⁺-DVR TODO). `B_cris = A_cris[1/t]` (inverting `t` already inverts `p`).
- **`B_cris^{Γ} = K₀`** (`K₀ = FractionRing (WittVector ℓ k(v))`) is **theorem provider N7**, never a
  structure field, never an assumed scalar identity, never a parameter. Until N7 lands every produced
  declaration speaks only of `FixedPoints.subring B Γ` (as `IsCrystallineRelQp` does).

---

## 6. Coefficient architecture — Qp-first, finite-`E` deferred

- **Bank now:** `E = ℚ_[ℓ]` exactly (`IsCrystallineRelQp`). `periodSubmodule` itself stays `E`-generic
  (it makes no dimension claim, so it is safe over any `E`); only the *predicate* is pinned to `ℚ_[ℓ]`.
- **Do NOT balance `B_cris` over ramified `E`.** For ramified `E/ℚ_[ℓ]`, `E` does not embed in `B_cris`
  (`B_cris ∩ K = K₀`), so `B_cris ⊗[E] V` is ill-formed and `(B_cris ⊗[ℚ_[ℓ]] V)^Γ` is a
  `K₀ ⊗[ℚ_[ℓ]] E`-module — stage-9's generic-`E` `IsCrystallineRel` conflated these and is retracted.
- **Deferred N-E:** `D` as a `K₀ ⊗[ℚ_[ℓ]] E`-module; crystallinity as freeness of rank `dim_E V`
  (equivalently `finrank_{K₀} D = [E:ℚ_[ℓ]] · dim_E V`). Not stated now.

---

## 7. Axiom-audit gate and probe plan

Under plan-mode I did **not** execute `lake` (writes build artifacts — non-read-only; this matches
stage-9's discipline). Bankability rests on (a) my independent read-only verification of every cited
declaration above, and (b) stage-12's recorded disposable-probe evidence
(`/tmp/fable5-g1-probes/P{0,0b,0c,1,2}`) auditing the exact declarations to
`[propext, Classical.choice, Quot.sound]`. **Mandatory execution-time gate (this synthesis does not
authorize it):**
1. Copy Blocks A–D into `FLTMethodology/Probes/MLTPadicHodgePeriodFunctor.lean`; register the import in
   `FLTMethodology.lean`.
2. Targeted `lake build` of that module.
3. `#print axioms` on **every** persisted declaration → require exactly
   `[propext, Classical.choice, Quot.sound]`; **any** `sorryAx`, `knownin1980s`, or custom axiom ⇒
   revert the slice and return REVISE with the failing declaration. Kernel output authoritative.
4. Keep `P0b.lean`/`P0c.lean` as expected-failure guards (synthesis must keep failing).
5. Do **not** promote `GaloisRep.IsCrystallineAt` until N3–N7 land.

---

## First genuine residual Lean goal (next open item after the slice)

The norm-equivariance step of **N-Cp**:
`∀ σ : PadicAlgCl ℓ ≃ₐ[ℚ_[ℓ]] PadicAlgCl ℓ, Isometry σ`, from uniqueness of the spectral-norm
extension (`spectralNorm.normedField` is the pinned instance), then
`UniformSpace.Completion.map`/`mapRingHom` extension to a continuous
`MulSemiringAction (Γ ℚ_[ℓ]) ℂ_[ℓ]`. (The *within-slice* first residual — already discharged in
stage-12 P2 — was the `smul_mem'` scalar-closure proof of `periodSubmodule`.)

---

## Stop-losses

1. **Never** introduce `SMul Γ (B ⊗[E] V)` (global or scope-leaking) — action diamond with
   `TensorProduct.leftHasSMul` under symmetric `SMulCommClass`. If a later node needs the action as an
   instance, use a **type synonym**.
2. **Never** name/define `K₀`-scalars on `periodSubmodule` before N7 — that is the exact stage-11
   failure mode. Use `FixedPoints.subring B Γ` throughout.
3. **Registration clash:** `FLTMethodology/Probes/MLTCoefficientData.lean` has now landed and touches
   `FLTMethodology.lean`. Rebase the new import, never force it; coordinate through the controller.
4. **N3–N7 are five separate providers.** Never estimate as one task; each gets its own review. If
   mathlib lands `A_cris`/PD-envelope upstream, adopt only on exact-declaration match at a new pin.
5. **Never** promote via `B_cris`-over-ramified-`E`; the finite-coefficient story is N-E over
   `K₀ ⊗[ℚ_[ℓ]] E` only.
6. **Prohibited in this slice and until N3–N8:** `IsCrystallineAt`, any comparison theorem, any T2
   assumption, any promotion of `FLT-MLT-PADIC-HODGE`.

---

## What this synthesis authorizes / does not

- **Authorizes:** handing the exact Block A–D slice + the deferred provider rows/edges to the mandatory
  independent GPT review (`next_gate`). Nothing else.
- **Does not authorize:** production build, graph/source-register/task-state mutation, `IsCrystallineAt`
  theorem, comparison theorem, T2 assumption, obligation promotion, or persisting any file.

**VERDICT: `READY-FOR-GPT-REVIEW`.**
