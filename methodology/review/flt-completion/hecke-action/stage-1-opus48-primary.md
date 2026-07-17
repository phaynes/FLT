# FLT-HECKE-ACTION — Early Interface Design (Primary)

**Component** `hecke-action` · **Obligation** `FLT-HECKE-ACTION` · **Work item** `FLT-414` ·
**Difficulty** 10 · **Wave** W04 (also W06 prereq) · **Design budget** 3600s · **Build gate** upstream.
**Target decl** `FLT.ModularityLifting.localizedHeckeAction` in module `FLT.ModularityLifting.Hecke`.
Read-only design. No source file edited. This freezes contracts for GPT independent review; **no build**.

---

## Context — why this obligation exists

The obligation record (`methodology/control/proof-obligations.ndjson:10`) states the deliverable is
*"a finite localized Hecke module, a complete local Hecke algebra `T`, and a proved surjective
compatible map `R → T` identifying Frobenius traces."* Its DoR row
(`methodology/control/source-design.ndjson:22`) is `BLOCKED`: only `proof_outline`,
`counterexample_review`, `library_matches` are satisfied; **`primary_source_exact`,
`hypothesis_translation`, `sublemma_graph`, `lean_signature` are still false**. Library probe
`MISS-004` = `absent`. Sources: **SRC-008** Wiles 1995, **SRC-009** Taylor–Wiles 1995,
**SRC-016** Taylor 2018 Thm 2.1.1.

The gap is a **bridge between two finished slabs**, not new machinery:

- **Downstream contract already exists (and is currently orphaned).** `FLT/Patching/REqualsT.lean:81,86`
  `ker_RtoT_le_nilradical` consumes an *abstract* `RtoT : R₀ →+* T₀` with
  `hRtoT : ∀ r (m : M₀), RtoT r • m = r • m` and concludes `RingHom.ker RtoT ≤ nilradical R₀`. It is
  sorry-free but **nothing imports it yet** — no `RtoT` consumer exists. `methodology/MLT-SOURCE-CONTRACT.md`
  names it the R=T *"signature stop point."* The C4 adapter below is designed to be its **first consumer**;
  `FLT-PATCHING` (`patched_point_factors_through_hecke`, proof pattern *"specialize the existing
  axiom-clean nilradical theorem"*) is the intended specialization, and `FLT-MLT` sits above it.
- **Integral Hecke slab already exists (sorry=0).**
  `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮` (`…/HeckeOperators/Concrete.lean:874`) is a
  `CommRing`, `IsNoetherianRing`, `Module.Finite 𝓞`, acting **faithfully** on the finite-free
  module `(U₁ 𝒮).toStruct.form D 𝓞` (`Basic.lean:564`, finite/free at `Basic.lean:861,865`), with
  operators `HeckeAlgebra.T` / `HeckeAlgebra.U` and `anemic` subalgebra (`Concrete.lean:911,918,1089`).
- **Normalization already fixed by the repo.** `GaloisRep.IsAutomorphicOfLevel`
  (`FLT/GaloisRepresentation/Automorphic.lean:70`) already pins the good-prime identities
  `trace_A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T … v hvS …)`, `(ρ.toLocal v (Frob v)).det =
  v.1.absNorm`, `ρ.IsUnramifiedAt v`, with `Frob = Field.AbsoluteGaloisGroup.adicArithFrob`
  (**arithmetic** Frobenius). The new T₀-valued contract **mirrors this exact convention**.

**Missing pieces (the definition-gap):** (1) localization at a maximal ideal `𝔪` of `T` giving a
complete-local `T₀` and finite `T₀`-module `M₀`; (2) a `T₀`-valued Galois-compatible action gluing
the eigenform-wise attached representations (`FLT-AUT-GALOIS`); (3) the classifying map `R → T₀` from
the `S`-good deformation ring, and its **surjectivity**; (4) module compatibility feeding
`ker_RtoT_le_nilradical`. The **analytic support** (existence of the attached representation, and
freeness/multiplicity-one of `M₀`) must stay **explicit**, never hidden in a top theorem.

## Dependency order (acyclic sublemma graph)

```
FLT-SUPPORT-AUTOMORPHIC (admitted)         adelic/automorphic support cluster
        │
FLT-AUT-DEF (proved)  GaloisRep.IsAutomorphicOfLevel   ← normalization anchor
        │
FLT-AUT-GALOIS (definition-gap)  FLT.Automorphic.attachedGaloisRepresentation   ← ATTACHED REP (support)
        │
FLT-SGOOD-SELECTED (definition-gap)  FLT.ModularityLifting.SelectedGood          ← local conditions
        │           (needs FLT-DEF-FUNCTOR: sGoodLiftFunctor_corepresentable — R exists)
        ▼
FLT-HECKE-ACTION      FLT.ModularityLifting.localizedHeckeAction   ← THIS
        │
        ├── FLT-PATCHING  patched_point_factors_through_hecke  (uses ker_RtoT_le_nilradical)
        └── FLT-MLT       modularity_lifting_weight_two_of_taylor2018
```

Direct deps recorded: `FLT-AUT-DEF, FLT-SGOOD-SELECTED, FLT-SUPPORT-AUTOMORPHIC, FLT-AUT-GALOIS`
(`proof-graph.ndjson:63–66`). `FLT-DEF-FUNCTOR` (`narrowSLiftUniversalRing`,
`Representable.lean:109`; corepresentability is itself `sorry` at `:104`) supplies `R` and is a
transitive prerequisite.

---

## Frozen contracts (target module `FLT/ModularityLifting/Hecke.lean`)

Signature-only at this stage (upstream-gated: bodies are `sorry`/deferred; the artifact is the
*interface*). Coefficient ring `𝓞` = complete local Noetherian `ℤ_[p]`-algebra with finite residue
field (the patching `Λ`); see **Open fork F2** for the `𝓞` vs `ℤ_[p]` choice.

### Shared context

```lean
namespace FLT.ModularityLifting
open TotallyDefiniteQuaternionAlgebra WeightTwoAutomorphicForm IsDedekindDomain NumberField
local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
variable {D : Type*} [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
  [IsQuaternionAlgebra.IsTotallyDefinite F D]
  [IsQuaternionAlgebra.NumberField.WithRigidification F D]
variable {p : ℕ} [Fact p.Prime]
variable {𝓞 : Type*} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [Algebra ℤ_[p] 𝓞]
  [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞] [CompactSpace 𝓞] [IsAdicTopology 𝓞]
variable (𝒮 : U₁Data F 𝓞 p)

/-- Integral Hecke module `S₂(U₁(S,Q); 𝓞)` (already finite-free over `𝓞`). -/
abbrev heckeModule := (U₁ 𝒮).toStruct.form D (M := 𝓞)
/-- Integral Hecke algebra `𝕋` (already `CommRing`, `IsNoetherianRing`, `Module.Finite 𝓞`). -/
abbrev heckeAlg := HeckeAlgebra D 𝒮
```

### C1 — Localized Hecke module and complete local Hecke algebra

`𝕋` is `Module.Finite` over complete-local `𝓞`, hence a finite product of complete-local rings;
localizing at a maximal ideal `𝔪` isolates one factor (already `𝔪`-adically complete).

```lean
variable (𝔪 : Ideal (heckeAlg (D := D) 𝒮)) [𝔪.IsMaximal]

/-- Complete local Hecke algebra `𝕋_𝔪` (obligation's "`T`"). -/
noncomputable abbrev heckeAlgLoc : Type _ := Localization.AtPrime 𝔪
/-- Finite localized Hecke module `M_𝔪` (obligation's localized module). -/
noncomputable abbrev heckeModuleLoc : Type _ := LocalizedModule 𝔪.primeCompl (heckeModule (D := D) 𝒮)

instance : IsLocalRing (heckeAlgLoc 𝒮 𝔪)                       := inferInstance
instance : Module.Finite 𝓞 (heckeAlgLoc 𝒮 𝔪)                  := /- finite factor -/  sorry
instance : Module.Finite (heckeAlgLoc 𝒮 𝔪) (heckeModuleLoc 𝒮 𝔪) := inferInstance
-- residue-characteristic side condition (non-vacuous localization):
def heckeAlgLoc.ResidueCharP : Prop := ringChar (IsLocalRing.ResidueField (heckeAlgLoc 𝒮 𝔪)) = p
```

### C2 — Galois-compatible action + trace/determinant compatibility  *(SUPPORT interface — explicit)*

The `T₀`-valued representation gluing the eigenform-wise attached reps of `FLT-AUT-GALOIS`. Trace/det
identities are **copied verbatim in shape** from `IsAutomorphicOfLevel` (only the target ring changes
from an eigenform `A` to `T₀`). Residual irreducibility is a **required** field (see counterexample X1).

```lean
/-- Attached local Galois action: a rank-2 free `𝕋_𝔪`-linear Galois representation whose Frobenius
traces/determinants realise the Hecke operators at good primes. This is the load-bearing analytic
input (Carayol/Taylor attachment + gluing); it is kept as an explicit interface, not a proof. -/
structure AttachedLocalGaloisRep
    (T₀ : Type*) [CommRing T₀] [TopologicalSpace T₀] [Algebra (heckeAlg (D := D) 𝒮) T₀]
    (V₀ : Type*) [AddCommGroup V₀] [Module T₀ V₀] [Module.Finite T₀ V₀] [Module.Free T₀ V₀] where
  rank_two   : Module.finrank T₀ V₀ = 2
  ρ          : GaloisRep F T₀ V₀
  /-- residual representation is (absolutely) irreducible — excludes Eisenstein `𝔪` (X1). -/
  residually_irreducible : GaloisRep.IsIrreducible
    (ρ.baseChange (IsLocalRing.ResidueField T₀))
  unramified : ∀ v, (p : 𝓞) ∉ 𝒮.S ∪ 𝒮.Q → (↑p ∉ v.asIdeal) → ρ.IsUnramifiedAt v
  det_frob   : ∀ v, ↑p ∉ v.asIdeal → v ∉ 𝒮.S → v ∉ 𝒮.Q →
    (ρ.toLocal v (Frob v)).det = (v.asIdeal.absNorm : T₀)
  trace_frob : ∀ v (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q), ↑p ∉ v.asIdeal →
    LinearMap.trace T₀ V₀ (ρ.toLocal v (Frob v)) = algebraMap (heckeAlg 𝒮) T₀ (HeckeAlgebra.T D 𝒮 v hvS hvQ)
  sgood      : SelectedGood ρ (𝒮.S)          -- the S-good local conditions (FLT-SGOOD-SELECTED)
```

### C3 — Deformation ring `R` and the surjective `R → T`

`R` is the `S`-good universal deformation ring of the residual rep (`FLT-DEF-FUNCTOR`,
`narrowSLiftUniversalRing`). Because the `AttachedLocalGaloisRep` `ρ` is itself an `S`-good
deformation over `T₀`, the universal property classifies it by a **unique local `𝓞`-algebra map**
`R → T₀`; surjectivity is because `T₀` is topologically generated over `𝓞` by the `Tᵥ` (and the
`Uᵥ` at `Q`), each hit by a Frobenius/`U`-trace of the universal deformation.

```lean
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra 𝓞 R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [IsAdicTopology R]

/-- Classifying map from the S-good deformation ring to the complete local Hecke algebra. -/
noncomputable def deformationClassifyingMap
    {T₀ V₀} [CommRing T₀] [TopologicalSpace T₀] [Algebra (heckeAlg (D := D) 𝒮) T₀] [Algebra 𝓞 T₀]
    [AddCommGroup V₀] [Module T₀ V₀] [Module.Finite T₀ V₀] [Module.Free T₀ V₀]
    (isUniv : /- R corepresents the S-good deformation functor of `Δ.ρ`'s residual rep -/ Prop)
    (Δ : AttachedLocalGaloisRep 𝒮 T₀ V₀) : R →+* T₀ := sorry

theorem deformationClassifyingMap_surjective … : Function.Surjective (deformationClassifyingMap …) := sorry
theorem deformationClassifyingMap_isLocalHom … : IsLocalHom (deformationClassifyingMap …) := sorry
```

### C4 — Top bundle `localizedHeckeAction` (the target declaration)

Bundles the localized module, the complete local `T`, the attached action, and the surjective
compatible `R → T` — packaged so its projection is *exactly* the `(RtoT, hRtoT)` input pair of
`ker_RtoT_le_nilradical`.

```lean
/-- **FLT-HECKE-ACTION.** Proposed data: the finite localized Hecke module `M₀` over the complete
local Hecke algebra `T₀`, together with a surjective, action-compatible `𝓞`-algebra map `R → T₀`
identifying Frobenius traces with Hecke operators. -/
structure localizedHeckeAction
    (𝔪 : Ideal (heckeAlg (D := D) 𝒮)) [𝔪.IsMaximal]
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra 𝓞 R]  … where
  T₀        : Type*; [instT : CommRing T₀]; …; algT : Algebra (heckeAlg 𝒮) T₀; loc : IsLocalization.AtPrime T₀ 𝔪
  M₀        : Type*; [instM : AddCommGroup M₀]; modT₀ : Module T₀ M₀; finM : Module.Finite T₀ M₀
  V₀        : Type*; …; freeV : Module.Free T₀ V₀
  attached  : AttachedLocalGaloisRep 𝒮 T₀ V₀
  RtoT      : R →+* T₀
  RtoT_surjective : Function.Surjective RtoT
  RtoT_isLocalHom : IsLocalHom RtoT
  /-- feeds `ker_RtoT_le_nilradical` `hRtoT` verbatim. -/
  smul_compat : ∀ (r : R) (m : M₀), RtoT r • m = r • m
```

### C5 — Analytic support obligations, kept explicit (never inside a top theorem)

Stated as **named hypotheses/axioms** so the audit sees them (T1 axiom policy). None is claimed proved.

```lean
/-- SUPPORT (FLT-AUT-GALOIS + FLT-SUPPORT-AUTOMORPHIC): the attached `T₀`-valued representation
exists, with rank-2 freeness / multiplicity-one of the localized module at a non-Eisenstein `𝔪`. -/
axiom exists_attachedLocalGaloisRep
    (𝔪 : Ideal (heckeAlg (D := D) 𝒮)) [𝔪.IsMaximal]
    (hchar : heckeAlgLoc.ResidueCharP 𝒮 𝔪) (hEis : /- 𝔪 non-Eisenstein -/ Prop) :
    ∃ V₀ (_ : AddCommGroup V₀) (_ : Module (heckeAlgLoc 𝒮 𝔪) V₀) (_ : Module.Free …),
      Nonempty (AttachedLocalGaloisRep 𝒮 (heckeAlgLoc 𝒮 𝔪) V₀)

/-- SUPPORT (multiplicity one / freeness): `M₀` is free over `𝓞 ⧸ Ann` and uniformly bounded —
the `Module.Free`/`UniformlyBoundedRank` hypotheses of `ker_RtoT_le_nilradical`. -/
axiom heckeModuleLoc_free … : Module.Free (𝓞 ⧸ Module.annihilator 𝓞 (heckeModuleLoc 𝒮 𝔪)) (heckeModuleLoc 𝒮 𝔪)
```

---

## Counterexamples / false-weakening probes

- **X1 (Eisenstein `𝔪`).** Drop `residually_irreducible` → a genuine rank-2 `GaloisRep F T₀ V₀`
  need not exist (only a pseudo-representation); multiplicity-one/freeness of `M₀` fails at Eisenstein
  `𝔪`. Contract **must** retain `residually_irreducible` (equivalently non-Eisenstein `𝔪`).
- **X2 (Frobenius normalization).** Using geometric instead of arithmetic Frobenius flips
  `det = Nv` to `det = Nv⁻¹`. Contract **reuses** `Field.AbsoluteGaloisGroup.adicArithFrob` and
  `(ρ.toLocal v (Frob v)).det = v.asIdeal.absNorm` verbatim from `IsAutomorphicOfLevel`.
- **X3 (nebentypus leak).** Weight-2 `U₁(S,∅)` with trivial character (`U₁Data … 1`) forces
  `det = Nv` with **no** `⟨v⟩` factor. Writing `det = Nv·χ(v)` is a false statement here.
- **X4 (wrong localization).** Localizing at a non-maximal or residue-char-`≠p` prime breaks
  complete-locality of `T₀` and the deformation universal property. Guarded by `[𝔪.IsMaximal]` +
  `heckeAlgLoc.ResidueCharP`.
- **X5 (surjectivity onto the wrong ring).** `R ↠ T₀` must land on the **local** factor `T₀`, and
  must cover the `Uᵥ` at `v ∈ Q` (Taylor–Wiles primes, obligation `FLT-TW-PRIMES`
  `exists_taylorWiles_primes`, absent), not only the anemic `Tᵥ`. If `Q ≠ ∅`, `anemic`-only
  generation is insufficient — the surjectivity proof must include the `U`-generators.
- **X6 (hiding support).** Folding `exists_attachedLocalGaloisRep` into `localizedHeckeAction`'s
  construction (rather than an explicit axiom/hypothesis) would let an unproved analytic input read as
  proved. Kept as a named `axiom`/field.

## Signature probes (cheap elaboration checks before any build)

- **P1** `#check @GaloisRep.IsAutomorphicOfLevel` and `#check ker_RtoT_le_nilradical` — confirm the
  `Frob`, `det = absNorm`, `trace`, and `(RtoT, hRtoT)` shapes the contract mirrors.
- **P2** `#check (inferInstance : Module.Finite 𝓞 (HeckeAlgebra D 𝒮))` and `… Free 𝓞 (form …)` —
  confirm the integral finiteness/freeness the localization inherits.
- **P3** `example : IsLocalRing (Localization.AtPrime 𝔪) := inferInstance` and
  `LocalizedModule 𝔪.primeCompl (heckeModule 𝒮)` typechecks with `Module.Finite`.
- **P4** `#check @LinearMap.trace`, `@GaloisRep.det`, `@GaloisRep.toLocal`, `@GaloisRep.IsUnramifiedAt`
  — confirm `AttachedLocalGaloisRep` fields elaborate against current `GaloisRep`.
- **P5** `#check @SelectedGood` / `@BlueprintSGood` — confirm `sgood` field target exists once
  `FLT-SGOOD-SELECTED` lands (currently definition-gap: probe will fail → gates the build).

## Bounded later build units (each signature-only until upstream lands)

| Unit | Content | Bound | Gated on |
|---|---|---|---|
| U1 | `Hecke.lean` skeleton + `heckeModule`/`heckeAlg` abbrevs + P1–P2 probes | ~40 loc | none |
| U2 | C1 localization layer (`heckeAlgLoc`, `heckeModuleLoc`, finiteness instances, `ResidueCharP`) | ~120 loc | none (Mathlib localization) |
| U3 | C2 `AttachedLocalGaloisRep` structure + P4 probes | ~90 loc | `FLT-SGOOD-SELECTED` (`SelectedGood`) |
| U4 | C5 explicit support `axiom`s (attachment + freeness) | ~50 loc | `FLT-AUT-GALOIS`, `FLT-SUPPORT-AUTOMORPHIC` |
| U5 | C3 `deformationClassifyingMap` + surjectivity/localHom statements | ~140 loc | `FLT-DEF-FUNCTOR` (`narrowSLiftUniversalRing`) |
| U6 | C4 `localizedHeckeAction` bundle + adapter lemma into `ker_RtoT_le_nilradical` inputs | ~110 loc | U2–U5 |

Total interface surface ≈ 550 loc of signatures (vs the record's proof estimate p50 30k / p95 500k
loc — the *interface* is bounded even though the *proof* is unbounded and upstream-gated).

## Verification (of the interface, pre-build)

Build is upstream-gated, so verification is elaboration + audit, not proof:
1. Run probes P1–P4 in a scratch `Hecke.lean` against current `main` (`base_sha 0272737`); P5 is
   expected-red and documents the `FLT-SGOOD-SELECTED` gate.
2. Confirm C4's projection unifies with `ker_RtoT_le_nilradical`'s `(RtoT, hRtoT)` by
   `example := @ker_RtoT_le_nilradical … (la.RtoT) (la.smul_compat)`.
3. Axiom-audit U4: the only new axioms are the two named analytic-support ones (plus repo-standard
   `propext/Classical.choice/Quot.sound`); nothing else may appear.

---

## Verdict: `READY-FOR-GPT-REVIEW`

The interface contracts (C1–C5), dependency order, counterexamples, probes, and bounded build units
are complete and **self-consistent**, and they are **anchored to already-accepted repository
conventions** (`IsAutomorphicOfLevel` for trace/det/Frobenius normalization; `REqualsT` for the
`(RtoT, hRtoT)` consumer shape; `HeckeAlgebra`/`form` for integral finiteness). All analytic inputs
are kept **explicit** (C5) rather than folded into a top theorem, and every body is deferred/`sorry`
under the upstream gate. This supplies the missing DoR `lean_signature` + `hypothesis_translation` +
`sublemma_graph` for independent GPT-5.6 review.

**Review-focus flags for GPT (the residual risk, not yet locked):**
1. **Genuine vs pseudo-representation** for the `T₀`-valued action (fork F1 below) — affects whether
   `AttachedLocalGaloisRep.ρ` is a `GaloisRep` or a determinant/pseudo-rep + reconstruction.
2. **`U`-generator surjectivity at Taylor–Wiles primes `Q`** (X5) — `anemic`-only is insufficient.
3. **Source exactness (SRC-016 warning).** Taylor 2018 does not directly yield the quaternionic
   `IsAutomorphicOfLevel` conclusion; the C2 identities inherit the repo's own convention, and the
   source-to-hypothesis exactness (`primary_source_exact`) is what review must certify.
4. **Coefficient ring** `𝓞` vs `ℤ_[p]` (fork F2) — must match the `Λ` actually used by `FLT-PATCHING`.

## Open design forks (surface to reviewer/user before build)

- **F1 — attached action model:** genuine `GaloisRep F T₀ V₀` (recommended default; requires
  `residually_irreducible`) **vs** pseudo-representation/determinant `Γ_F → T₀` (works at Eisenstein
  `𝔪` but needs a reconstruction lemma for `M₀`-freeness).
- **F2 — coefficient ring:** general complete-local `𝓞`/`ℤ_[p]`-algebra (recommended, matches
  patching `Λ`) **vs** hardcode `ℤ_[p]` (matches current `IsAutomorphicOfLevel` literally, less
  general).
