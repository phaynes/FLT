# Stage 1 Fable 5 alternative design — Moret–Bailly

## Model and transport evidence

- Agent: `fable5-designer-d10`
- Configured model: `claude-fable-5`
- Backend transport: Claude CLI through `kg-model_bridge`
- Role: independent Stage-1 diversity designer
- Review budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `1129.367 s`
- Token count: `45,058` input; `325,663` cache-create; `2,942,172` cache-read; `90,400` output; `3,403,293` total including cache, deduplicated over `61` request IDs
- Output characters: `15,373` bridge response; full plan preserved below
- Claude session: `649070fe-b9f0-44d3-a437-5d6707d945a4`
- Prompt: `methodology/review/flt-completion/moret-bailly/stage-1-prompt-fable5.md`
- Repository mutation authority: read-only; no model edits permitted
- Verdict: `INTERFACE-FIRST`

## Full independent design

# INDEPENDENT STAGE-1 DESIGN — FLT-MORET-BAILLY

Repository: `/Volumes/second-store/devel/proof-forks/FLT`, branch
`methodology/varro-proof-program-20260716`, start SHA `827eb96`. Read-only; no files edited.
Independence honored: `stage-1-opus48-primary.md`, `stage-1-attempts.md`, the other Stage-1
prompts' outputs, and everything under `review/flt-completion/class-field/` were **not** read.
Pinned Mathlib: `.lake/packages/mathlib` @ `a3364faec42918fcd84a03a255b50570129f9ead`.

## Context

`FLT-MORET-BAILLY` (proof-obligations.ndjson:16) is the T2-target obligation
`FLT.PotentialModularity.moret_bailly_point`, source SRC-011 (L. Moret-Bailly, *Groupes de Picard
et problèmes de Skolem I, II*, Ann. Sci. ENS 22 (1989), 161–194), expected module
`FLT.PotentialModularity.MoretBailly`, current state `absent`, DoR `BLOCKED` with only
`primary_source_exact: true` (source-design.ndjson:27). Its direct consumers are
`FLT-AUX-LOCAL-FIELD` (`AuxiliaryFieldCondition`, deps `[FLT-MLT-SOURCE, FLT-MORET-BAILLY]`) and
`FLT-AUX-CURVE` (`exists_auxiliary_curve`, deps `[FLT-MORET-BAILLY, FLT-CLASS-FIELD,
FLT-AUX-LOCAL-FIELD]`); transitively `FLT-RESIDUAL-IMAGE` and `FLT-POTMOD`. This document is the
required independent Stage-1 design under the tri-design-synthesis-build pipeline.

---

## 1. VERDICT

**INTERFACE-FIRST.** The source statement cannot elaborate in the pinned libraries today for one
structural reason: there is no v-adic topology on the K_v-points of a scheme (pinned Mathlib has
only the Zariski topology on the underlying space; NONE FOUND for point-set topology), so
"nonempty open Ω_v ⊆ X(K_v)" is currently unstatable. Every other ingredient exists pinned
(`Scheme.Over` + `X ↘ S`, `Smooth`/`SmoothOfRelativeDimension 1`, `GeometricallyConnected`,
`HeightOneSpectrum.adicCompletion`, FLT's `v.Extension`/`adicCompletionSemialgHom`/
`baseChangeAlgEquiv`, `InfinitePlace` + `IsTotallyReal` + `IsUnramified`,
`IntermediateField.LinearDisjoint`, `moduleTopology`), and a sound, cheap, canonical construction
of the missing topology exists (final topology from affine-open algebra-hom spaces; valid because
K_v-points of a scheme factor through affine opens since `Spec K_v` is a point). Independently of
the interface, T2 axiom admission is hard-gated: the Moret-Bailly 1989 text is **not locally
available** (whole-repo search: only the BibTeX stub `blueprint/src/FLT.bib:64` and prose), and
`control/historical-assumptions.ndjson` (`HIST-UNRESOLVED`) forbids any T2 assumption until an
exact Lean type **and** primary-source locator are independently reviewed. So: build the
local-point interface and contract-independent adapters now; admit the axiom only after the
source gate clears. Not `OBSTRUCTION`: no discovered fact blocks the interface path. Not
`DESIGN-VIABLE`-as-stated: a design that wrote the axiom today would either fail to elaborate or
have to smuggle in an unsound topology parameter (see §7, CX-0).

---

## 2. CURRENT EXACT BOUNDARY

Present (exact, verified in this session):
- Blueprint statement of the theorem, `\notready`, `blueprint/src/chapter/chtopbestiary.tex:255-266`
  (quoted in §3), plus the consumer prose `ch04overview.tex:21-25, 93-100`. The blueprint itself:
  "we do not even have the definition of a curve over a field in Lean."
- Axiomatization convention: `FLT/Assumptions/` one named axiom per file with reference
  (`Mazur_statement`, `Odlyzko_statement`); `knownin1980s` generic axiom + tactic
  (`FLT/Assumptions/KnownIn1980s.lean:79`) permitted only at T1. `FLT/Assumptions/README.md:36-40`
  already lists Moret-Bailly as a pending formalizable assumption, and — separately — "existence
  of a solvable extension … prescribed behaviour … class field theory" (do not conflate; §7 CX-8).
- Consumer Lean anchors: `GaloisRep` (`FLT/Deformations/RepresentationTheory/GaloisRep.lean:47`),
  `WeierstrassCurve.galoisRep` (`FLT/EllipticCurve/Torsion.lean:487`), `IsHardlyRamified`
  (`FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96`), `GaloisRep.IsAutomorphicOfLevel`
  (`FLT/GaloisRepresentation/Automorphic.lean:70` — quaternionic, requires totally real F; its
  docstring's totally-definite discriminant-1 D forces **even degree**), `cyclic_base_change`
  (`Automorphic.lean:137`, sorried, requires `[IsGalois F E] [IsSolvable]`, `Even finrank`).
- Completion/extension toolkit (FLT, all kernel-present):
  `v.Extension B := {w // w.under A = v}` (`FLT/DedekindDomain/IntegralClosure.lean:40`);
  `adicCompletionSemialgHom : v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L`
  (`FLT/DedekindDomain/Completion/BaseChange.lean:182`, continuity `:196`);
  `baseChangeAlgEquiv : L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L`
  (`:778`, continuous variant `:785`); `ramificationIdx_eq_ramificationIdx` (`:676`);
  `InfinitePlace.Extension` (`FLT/NumberField/InfinitePlace/Extension.lean:151`) with
  ramified/unramified split (`:249,:254`).
- Pinned Mathlib: full list in §6.

Absent (verified NONE FOUND):
- Any `FLT/PotentialModularity/` module or any of the three target declarations.
- v-adic topology on `X(K_v)`; any rational-points type; `Variety`; MB theorem; existence of
  (totally real) extensions with prescribed local behaviour; strong approximation; Shimura/moduli;
  `TateModule`; `LinearDisjoint` usage anywhere in FLT.
- The Moret-Bailly 1989 paper text (no PDF/scan anywhere in the repo).

Policy boundary: T2 = "finite, named, exactly typed, sourced historical assumptions", no generic
`knownin1980s` (`methodology/spec/flt-proof-program.instances.json`; TRACEABILITY.md:57-61);
`HIST-UNRESOLVED` blocks admission today. FLT-MORET-BAILLY `completion_targets: [T2, T3]` — the
same statement must later be *proved* under the standard trio, so the statement must be one the
programme is prepared to prove, not merely to cite (bias toward the narrowest consumer-sufficient
form).

---

## 3. SOURCE AND CONSUMER AUDIT

### 3.1 Source theorem and locator

SRC-011: L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem I, II*, Ann. Sci. ENS (4) 22
(1989), no. 2, 161–194. Register state: "Primary source identified; exact Lean statement absent."
**The paper is not locally available; the exact théorème number is unverified.** The repository's
working statement is the blueprint's (chtopbestiary.tex:255-266, verbatim content):

> Let K^avoid/K be a Galois extension of number fields, S a finite set of places of K. For v ∈ S
> let L_v/K_v be a finite Galois extension. Let T/K be a smooth, geometrically connected curve;
> for each v ∈ S let Ω_v ⊆ T(L_v) be a nonempty, Gal(L_v/K_v)-invariant, open subset. Then there
> is a finite Galois extension L/K and P ∈ T(L) such that: L/K is linearly disjoint from K^avoid
> over K; for v ∈ S and w | v, L_w/K_v ≅ L_v/K_v; and P ∈ Ω_v ⊆ T(L_v) ≅ T(L_w) via such a
> K_v-algebra isomorphism.

Condition-by-condition translation and verification status:

| # | Source condition (blueprint form) | Lean translation | Verified against primary text? |
|---|---|---|---|
| H1 | K number field | `[Field K] [NumberField K]` | citation-level only |
| H2 | K^avoid/K finite Galois | `Kav : IntermediateField K Kbar`, `[FiniteDimensional K Kav]`, `[IsGalois K Kav]` | **UNVERIFIED** — 1989 statement's disjointness clause not sighted; possibly a later refinement (see gate SG-1) |
| H3 | T/K smooth | `[Smooth (X ↘ Spec (.of K))]` | citation-level |
| H4 | geometrically connected **curve** | `[GeometricallyConnected (X ↘ …)]` + `[SmoothOfRelativeDimension 1 (X ↘ …)]` | **UNVERIFIED** — MB is usually cited for varieties; curve is a blueprint narrowing (safe: weaker axiom) |
| H5 | finite type / quasi-projective? | `[LocallyOfFiniteType …]` (+ `[QuasiCompact …]` probe) | **UNVERIFIED** — quasi-projectivity hypothesis unknown without text |
| H6 | S finite, places incl. archimedean | `Sf : Finset (HeightOneSpectrum (𝓞 K))`, `Si : Finset (InfinitePlace K)` (no unified place type pinned) | **UNVERIFIED** whether 1989 covers archimedean prescriptions |
| H7 | L_v/K_v finite Galois prescribed | `FinitePrescription` bundle (§5, N4); topology = `moduleTopology (v.adicCompletion K) M` | **UNVERIFIED** (prescribed-extension variant vs plain total splitting) |
| H8 | Ω_v nonempty, open, Gal(L_v/K_v)-invariant | fields `nonempty`, `isOpen` (in the canonical v-adic point topology, §5 N1), `galoisStable` | invariance clause: citation-level |
| C1 | L/K finite Galois | `∃ L : IntermediateField K Kbar, FiniteDimensional K L ∧ IsGalois K L` | **UNVERIFIED** — Galois-ness of L is load-bearing (§7 CX-3); must be confirmed in the exact source or the derivation chain repaired |
| C2 | L linearly disjoint from K^avoid | `L.LinearDisjoint Kav` (`Mathlib/FieldTheory/LinearDisjoint.lean:157`) | **UNVERIFIED** (as H2) |
| C3 | ∀ v ∈ S, ∀ w \| v: L_w ≅ L_v over K_v | `∀ w : v.Extension (𝓞 L), Nonempty (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] M_v)` | citation-level |
| C4 | P ∈ T(L) with image in Ω_v for every w \| v, via any K_v-iso | `∃ P : X.ptsOver K L, ∀ v w e, ptsMap (e.symm) (localize w P) ∈ Ω_v` (∀-e form; equivalent to ∃-e under H8 invariance) | citation-level |

Provenance risk recorded honestly: the commonly cited 1989 locator is Théorème 1.3 of Skolem II
(sometimes the variant with prescribed local extensions and the linear-disjointness refinement is
attributed to MB *plus* a derivation stated in later literature, e.g. Taylor's potential-modularity
papers). Until the paper (and, if needed, the secondary derivation) is in
`methodology/evidence/sources/`, `hypothesis_translation` cannot be set true and no axiom may be
admitted. This is **gate SG-1**, and it is consistent with the register's own warning that
"Primary source identified" is weaker than "visually checked."

### 3.2 Consumer inventory (exact, from control rows + Lean/blueprint surface)

| Consumer need | Needed by (exact) | Owner |
|---|---|---|
| L totally real | `exists_auxiliary_curve` (FLT-AUX-CURVE row); `IsAutomorphicOfLevel`'s `[IsTotallyReal F]`; `Deformations/Representable.lean:49` | **Source thm**, via archimedean prescriptions Si = all real places, trivial L_v (K=ℚ: the one real place) |
| ℓ (and auxiliary p) unramified in L | MLT contract hyp 5 (`MLT-SOURCE-CONTRACT.md`: "ell unramified in F"); FLT-AUX-LOCAL-FIELD row | **Source thm** supplies prescribed unramified L_v at v ∈ {ℓ, p}; **adapter A1** converts "all completions ≃ unramified M_v" into the arithmetic predicate (`Algebra.IsUnramifiedAt` / `ramificationIdx' = 1`) |
| witness unramified at v \| ℓ (Taylor 2018 hyp 7, at-ℓ; the gpt56xhigh correction) | FLT-POTMOD's two Taylor applications | **Consumer** (FLT-AUX-CURVE): follows from good reduction of A above ℓ, p — i.e. from choosing Ω_v inside the good-reduction locus; NOT a field condition and NOT in MB |
| complete splitting at ℓ | nothing (Taylor 2006 Thm 3.3 route, **rejected**; CONVERGENCE.md; risk R4) | nobody — must NOT appear as a consumer requirement; MB *can* prescribe it (L_v = K_v) but no consumer may demand it |
| L Galois over ℚ | FLT-AUX-CURVE row; blueprint ch04overview:21-25 | **Source thm** (C1) — provided the exact source really yields Galois L (SG-1); otherwise redesign, since Galois closure post hoc destroys disjointness (§7 CX-3) |
| L linearly disjoint from K(ker ρ̄)·ℚ(ζ_ℓ)-type avoidance compositum | FLT-RESIDUAL-IMAGE ("Moret-Bailly disjointness preserves each concrete image"); FLT-AUX-LOCAL-FIELD ("disjoint from the two residual/cyclotomic avoidance extensions") | **Source thm** (C2) against ONE compositum K^avoid; **consumer** builds the compositum (§7 CX-2: pairwise is insufficient) |
| even degree [L:ℚ] | `IsAutomorphicOfLevel` (totally definite discriminant-1 quaternion algebra forces even |ram| = degree); `cyclic_base_change` hyp; FLT-AUX-CURVE row | **Project adapter A2** (quadratic enlargement preserving all other conditions); NOT a source conclusion |
| quaternionic splitting behaviour | JL/`IsAutomorphicOfLevel` consumers | **Consumer** side; determined by even degree + level data; never in MB |
| good reduction of A above ℓ, p | FLT-AUX-LOCAL-FIELD row; supplies Taylor hyp 7 via the moduli dictionary | **Consumer** (FLT-AUX-CURVE): encoded in the CHOICE of Ω_v (good-reduction locus), plus the moduli-point ↔ curve dictionary; MB only transports membership in Ω_v |
| Ω_v nonempty (local solvability of the moduli problem) | MB hypothesis H8 | **Consumer** obligation (local constructions / FLT-CLASS-FIELD side); MB must EXPOSE it as a hypothesis, never discharge it (§7 CX-5, CX-9) |
| A/L with mod-ℓ rep ≅ ρ̄\|G_L, mod-p induced | FLT-AUX-CURVE lean_type; blueprint ch04overview:93-100 | **Consumer**: the moduli curve construction + dictionary (separate, huge obligation; not designed here) |
| solvable L | nothing in this route (`cyclic_base_change` concerns other extensions) | nobody — MB cannot supply solvability; conflation with the Assumptions-README class-field item is a design error (§7 CX-8) |

Why no project conclusion leaks into the source layer: the source theorem's output is exactly
(L Galois, disjoint, prescribed completions, point in the opens). Total reality is not a special
clause — it is the instantiation of prescriptions at archimedean places. Unramifiedness at ℓ is
not a clause — it is the instantiation of H7 with unramified M_v plus adapter A1. Even degree,
good reduction, residual matchings, quaternionic data appear only in adapters/consumers.

---

## 4. DEPENDENCY GRAPH (transitively reduced)

```
N0 algHomTopology (pointwise-convergence topology on A →ₐ[K] R)          [buildable now]
 └→ N1 Scheme.ptsOver + canonical v-adic TopologicalSpace instance       [buildable now]
     └→ N2 ptsOver functoriality (ptsMap), continuity, AlgEquiv action   [buildable now]
         └→ N3 local transport: X(L) → X(L_w); X(M_v) ≃ X(L_w) along
               continuous K_v-algebra isos (uses FLT adicCompletionSemialgHom,
               moduleTopology; infinite-place analogue via v.Completion)  [buildable; small risk: instance diamonds]
             └→ N4 FinitePrescription / RealPrescription bundles          [buildable]
                 └→ N5 moret_bailly_point STATEMENT (elaboration probe)   [gate SG-3]
                     └→ N6 axiom admission (FLT/Assumptions/MoretBailly.lean
                           + historical-assumptions row)                  [gates SG-1, SG-2 — HARD]
A1 split/unramified arithmetic bridges (≃-completions ⇒ ramificationIdx=1;
   splitsCompletely ⇒ unramified as a lemma, never a rename)              [independent; buildable now]
A2 even-degree quadratic enlargement (∃ real quadratic Q split at Sf,
   jointly disjoint from L·K^avoid; compositum preserves all conditions)  [needs weak-approx-level lemma; possibly FLT-CLASS-FIELD-owned]
A3 AuxiliaryFieldCondition structure (FLT-AUX-LOCAL-FIELD)                [needs N5 vocabulary + gate SG-4 (FLT-MLT-SOURCE vocabulary freeze)]
A4 exists_auxiliary_curve (FLT-AUX-CURVE)                                 [needs N6, A2, A3 + moduli curve obligation — out of scope; gate SG-5]
```

Build gates: SG-1 source text; SG-2 HIST-UNRESOLVED policy review; SG-3 N5 elaboration probes;
SG-4 MLT vocabulary (MLT-SOURCE-CONTRACT: "Only after those signatures are kernel-green may
FLT-MLT-SOURCE be frozen"); SG-5 moduli-curve shape verification. Details in §9.

Local-open construction (the load-bearing new mathematics of the interface): since K_v is a
field, `Spec K_v` is a one-point scheme, so every K_v-point of X factors through an affine open.
Define the topology on `X.ptsOver K R` (R a topological field K-algebra) as the **final topology**
of the family `(Γ(X,U) →ₐ[K] R) → X.ptsOver K R` over `U : X.affineOpens`, where each hom-space
carries the topology induced from `A → R` with the product topology (`Pi.topologicalSpace`).
This is generator-independent, needs no immersion into ℙⁿ, no gluing lemmas for the *statement*,
and coincides with the classical v-adic topology for finite-type X (the agreement lemma is later,
T3-side work, not needed to state or admit the axiom). Zariski topology on `X.carrier` plays no
role and must not be confused with this (§6).

---

## 5. PROPOSED LEAN SIGNATURES (dependency order)

Module: `FLT/PotentialModularity/MoretBailly/LocalPoints.lean` (N0–N4),
`FLT/PotentialModularity/MoretBailly.lean` (N5), `FLT/Assumptions/MoretBailly.lean` (N6, gated),
`FLT/PotentialModularity/AuxiliaryField.lean` (A1–A3, partially gated).

```lean
-- ===== N0 =====
namespace FLT.PotentialModularity.MoretBailly

/-- Pointwise-convergence topology on K-algebra homomorphisms into a topological ring. -/
noncomputable def algHomTopology (K A R : Type*) [CommSemiring K] [Semiring A] [Algebra K A]
    [Semiring R] [Algebra K R] [TopologicalSpace R] : TopologicalSpace (A →ₐ[K] R) :=
  TopologicalSpace.induced (⇑· : (A →ₐ[K] R) → (A → R)) Pi.topologicalSpace

-- ===== N1 =====
open AlgebraicGeometry CategoryTheory

/-- R-points of a K-scheme X (R a K-algebra): morphisms Spec R ⟶ X over Spec K. -/
def _root_.AlgebraicGeometry.Scheme.ptsOver (X : Scheme.{u}) (K : Type u) [Field K]
    [X.Over (Spec (CommRingCat.of K))] (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  { f : Spec (CommRingCat.of R) ⟶ X //
      f ≫ (X ↘ Spec (CommRingCat.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K R)) }

/-- A field-valued point factors through an affine open; the map from affine-local points. -/
noncomputable def ptsOfAffine (U : X.affineOpens) (R : Type u) [Field R] [Algebra K R] :
    (Γ(X, U.1) →ₐ[K] R) → X.ptsOver K R := …

/-- Canonical (v-adic-style) topology on field-valued points: final topology from all
    affine-open hom-spaces. NOT the Zariski topology, NOT a parameter. -/
noncomputable instance (R : Type u) [Field R] [Algebra K R] [TopologicalSpace R]
    [IsTopologicalRing R] : TopologicalSpace (X.ptsOver K R) :=
  ⨆ U : X.affineOpens, .coinduced (ptsOfAffine (K := K) (X := X) U R)
    (algHomTopology K Γ(X, U.1) R)

-- ===== N2 =====
/-- Functoriality along K-algebra maps of fields (precomposition with Spec.map). -/
def ptsMap {R S : Type u} [Field R] [Algebra K R] [Field S] [Algebra K S]
    (φ : R →ₐ[K] S) : X.ptsOver K R → X.ptsOver K S :=
  fun f => ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f.1, by …⟩

theorem continuous_ptsMap … (hφ : Continuous φ) : Continuous (ptsMap (X := X) φ) := …

/-- Action of continuous K-algebra automorphisms by homeomorphisms. -/
noncomputable def ptsEquiv {R : Type u} … (σ : R ≃ₐ[K] R) (hσ : Continuous σ) :
    X.ptsOver K R ≃ₜ X.ptsOver K R := …

-- ===== N3 (finite places; infinite analogue with v.Completion) =====
open IsDedekindDomain HeightOneSpectrum NumberField

-- For L : IntermediateField K Kbar finite over K, w : v.Extension (𝓞 L):
-- localization X(L) → X(L_w) via the K-algebra map L →ₐ[K] w.1.adicCompletion L, and
-- transport X(L_w) ≃ₜ X(M_v) along a continuous (v.adicCompletion K)-algebra iso, restricted
-- to K-algebra maps via IsScalarTower K (v.adicCompletion K) M_v.  [instance-diamond probe]

-- ===== N4 =====
variable (K : Type u) [Field K] [NumberField K]
variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]

/-- A prescribed local condition at a finite place: a finite Galois extension of K_v and a
    nonempty, open, Galois-stable set of M-points. Topology on M: `moduleTopology K_v M`. -/
structure FinitePrescription (v : HeightOneSpectrum (𝓞 K)) where
  M : Type u
  [fieldM : Field M]
  [algKv : Algebra (v.adicCompletion K) M]
  [fd : FiniteDimensional (v.adicCompletion K) M]
  [gal : IsGalois (v.adicCompletion K) M]
  [algK : Algebra K M]
  [tower : IsScalarTower K (v.adicCompletion K) M]
  Ω : Set (X.ptsOver K M)            -- with letI := moduleTopology (v.adicCompletion K) M
  isOpen : IsOpen Ω
  nonempty : Ω.Nonempty
  galoisStable : ∀ σ : M ≃ₐ[v.adicCompletion K] M, ptsEquiv … σ … '' Ω = Ω

/-- Prescription at a real place, trivial local extension (the totally-real instantiation;
    a documented specialization of the source's archimedean clause — see §11 Q3). -/
structure RealPrescription (v : InfinitePlace K) where
  isReal : v.IsReal
  Ω : Set (X.ptsOver K v.Completion)
  isOpen : IsOpen Ω
  nonempty : Ω.Nonempty

-- ===== N5 — the source-faithful statement =====
variable (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]

theorem moret_bailly_point
    (Kav : IntermediateField K Kbar) [FiniteDimensional K Kav] [IsGalois K Kav]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]      -- "curve"
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [QuasiCompact (X ↘ …)]
    (Sf : Finset (HeightOneSpectrum (𝓞 K))) (Pf : ∀ v ∈ Sf, FinitePrescription K X v)
    (Si : Finset (InfinitePlace K))          (Pi : ∀ v ∈ Si, RealPrescription K X v) :
    ∃ (L : IntermediateField K Kbar) (_ : FiniteDimensional K L) (_ : IsGalois K L),
      L.LinearDisjoint Kav ∧
      (∀ v (hv : v ∈ Sf) (w : v.Extension (𝓞 L)),
        Nonempty (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] (Pf v hv).M)) ∧
      (∀ v (hv : v ∈ Si) (w : InfinitePlace L), w.comap (algebraMap K L) = v → w.IsReal) ∧
      ∃ P : X.ptsOver K L,
        (∀ v (hv : v ∈ Sf) (w : v.Extension (𝓞 L))
           (e : (Pf v hv).M ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),
           ptsMap (localizeAlgHom L w) P ∈ (fun q => ptsEquiv … e.symm … q) ⁻¹' … (Pf v hv).Ω) ∧
        (∀ v (hv : v ∈ Si) (w : InfinitePlace L) (hw : w.comap (algebraMap K L) = v) …,
           /- image of P in X(v.Completion) via the real completion identification -/
           … ∈ (Pi v hv).Ω)
-- Note: the ∀-e form is the strong, well-posed reading; under galoisStable it is equivalent
-- to any single-e form. Never state ∃-e without invariance (§7 CX-4).

-- ===== N6 — gated axiom (NOT to be added until SG-1/SG-2 clear) =====
-- FLT/Assumptions/MoretBailly.lean, repo convention:
-- axiom MoretBailly_statement : <exactly the N5 Π-type>
-- theorem FLT.PotentialModularity.moret_bailly_point … := MoretBailly_statement …
-- plus a historical-assumptions.ndjson row with the reviewed primary locator.

-- ===== A1 — arithmetic bridges (independent of N5/N6; buildable now) =====
/-- If every completion of L above v is K_v-isomorphic to an unramified extension of K_v,
    then v is unramified in L. -/
theorem unramifiedIn_of_completions_unramified … := …
/-- Complete splitting (M = K_v) implies unramifiedness — an implication lemma, never a
    definitional substitution (risk R4). -/
theorem unramifiedIn_of_splitsCompletely … := …

-- ===== A2 — even-degree enlargement (project adapter) =====
/-- Given the MB output field L (totally real, Galois, disjoint from Kav, prescribed completions
    at Sf), there is a totally real quadratic Q/ℚ split at every rational prime below Sf and
    jointly linearly disjoint from L ⊔ Kav; L' := L ⊔ Q has even degree and retains every
    condition, and X-points transport along L ↪ L'. -/
theorem exists_evenDegree_enlargement … := …

-- ===== A3 — FLT-AUX-LOCAL-FIELD structure (signature FROZEN ONLY after SG-4) =====
/-- Source-track vs project-track field conditions, kept as separate named fields. -/
structure AuxiliaryFieldCondition (F : IntermediateField ℚ Kbar) (ℓ p : ℕ) … where
  -- source-track (supplied by moret_bailly_point + A1/A2):
  totallyReal   : IsTotallyReal F
  galois        : IsGalois ℚ F
  unramified_ℓ  : … -- v(ℓ) unramified in F (Algebra.IsUnramifiedAt spelling)
  unramified_p  : …
  disjoint      : F.LinearDisjoint Kavoid   -- Kavoid = the ONE avoidance compositum
  -- project-track (JL/quaternionic requirements, never claimed from the source):
  evenDegree    : Even (Module.finrank ℚ F)
  -- curve-track lives in FLT-AUX-CURVE (good reduction of A above ℓ, p from the Ω_v choice).
```

Signature probes (to run as `#check`/elaboration probes outside the repo before any freeze):
P1 `Scheme.Over`/`X ↘ S` + `Spec (CommRingCat.of K)` universe behaviour at `Type 0` vs `Type u`;
P2 `SmoothOfRelativeDimension 1` + `GeometricallyConnected` on a structure morphism together;
P3 the `IsScalarTower K (v.adicCompletion K) M` instance path and diamond-freedom with
`moduleTopology`; P4 `IntermediateField.LinearDisjoint` binder shapes for two intermediate
fields of `Kbar`; P5 `v.Extension (𝓞 L)` where `L : IntermediateField K Kbar` (does
`Algebra (𝓞 K) (𝓞 L)` resolve?); P6 `InfinitePlace.comap`/`IsReal` transport to `v.Completion ≃+* ℝ`
(`ringEquivRealOfIsReal`); P7 `Algebra.IsUnramifiedAt` spelling for `𝓞 ℚ → 𝓞 F` vs
`Ideal.ramificationIdx'` (FLT `Completion/BaseChange.lean:676` connects the two worlds);
P8 `pointsPi` applicability if the tensor-form corollary (`X(L ⊗ K_v) → Π X(L_w)`) is wanted.

---

## 6. LIBRARY MATCHES (pinned; NONE FOUND stated explicitly)

| Node needs | Pinned match | Locator |
|---|---|---|
| scheme + structure morphism | `AlgebraicGeometry.Scheme`, `Scheme.Over`, `X ↘ S` | `Scheme.lean:42`; `AlgebraicGeometry/Over.lean:36` |
| smooth | `AlgebraicGeometry.Smooth` (`IsSmooth` deprecated 2026-02-09) | `Morphisms/Smooth.lean:62` |
| curve (relative dim 1) | `SmoothOfRelativeDimension` | `Morphisms/Smooth.lean:135` |
| geometrically connected | `AlgebraicGeometry.GeometricallyConnected` | `Geometrically/Connected.lean:40` (also Integral/Irreducible/Reduced) |
| finite type | `LocallyOfFiniteType` (+ `QuasiCompact`) | `Morphisms/FiniteType.lean:43` |
| `Variety` | **NONE FOUND** (compose Scheme + classes) | — |
| points functor fact | `AlgebraicGeometry.pointsPi` | `PointsPi.lean:100` |
| **topology on X(K_v)** | **NONE FOUND** — only Zariski on the carrier; v-adic point topology must be built (N0/N1). Zariski openness of subschemes ≠ v-adic openness of point sets; the design never uses `X.Opens` for Ω_v | — |
| number field, places | `NumberField`, `InfinitePlace` (+ `IsReal`, `comap`), `FinitePlace` | `NumberField/Basic.lean:43`; `InfinitePlace/Basic.lean:57` |
| totally real | `NumberField.IsTotallyReal` | `InfinitePlace/TotallyRealComplex.lean:47` |
| K_v (finite) | `HeightOneSpectrum.adicCompletion` | `DedekindDomain/AdicValuation.lean:605` |
| K_v (infinite) | `InfinitePlace.Completion`, `ringEquivRealOfIsReal` | `NumberField/Completion/InfinitePlace.lean:81` |
| w over v (finite) | FLT `v.Extension B` (`w.under A = v`) | `FLT/DedekindDomain/IntegralClosure.lean:40` |
| K_v → L_w, continuous | FLT `adicCompletionSemialgHom` (+ `_continuous`) | `FLT/DedekindDomain/Completion/BaseChange.lean:182,196` |
| L ⊗[K] K_v ≅ Π L_w | FLT `baseChangeAlgEquiv` / `baseChangeContinuousAlgEquiv` | ibid.:778, 785 |
| ramification transfer local↔global | FLT `ramificationIdx_eq_ramificationIdx`, `ramificationIdx_mul_inertiaDeg_eq_finrank` | ibid.:676, 736 |
| w over v (infinite) | FLT `InfinitePlace.Extension`, `IsUnramified/IsRamified` split | `FLT/NumberField/InfinitePlace/Extension.lean:151,249,254`; Mathlib `InfinitePlace/Ramification.lean:184` |
| linear disjointness | `IntermediateField.LinearDisjoint` (+ Subalgebra level) | `FieldTheory/LinearDisjoint.lean:157` |
| unramified (finite) | `Algebra.IsUnramifiedAt`; `¬ P ∣ differentIdeal` iff; `ramificationIdx = 1` iff | `Unramified/Locus.lean:45`; `Different.lean:911`; `RamificationInertia/Ramification.lean:107` |
| complete splitting | ⚠ only `Algebra.IsFiniteSplit` (algebra-level) | `TotallySplit.lean:37` — no per-prime predicate; A1 states its own lemma |
| module topology on M/K_v | `moduleTopology` | `Topology/Algebra/Module/ModuleTopology.lean:128` |
| weak approximation (adapter A2 support) | `denseRange_algebraMap_pi` (finite families of inequivalent absolute values) | `Analysis/AbsoluteValue/Equivalence.lean:407`; NumberField versions `InfinitePlace/Basic.lean:605` |
| strong approximation | **NONE FOUND** | — |
| totally real ext. with prescribed local behaviour (the theorem itself) | **NONE FOUND** anywhere (Mathlib, FLT, AINTLIB, HasseWeil) | — |
| good reduction (consumer side) | `WeierstrassCurve.HasGoodReduction` | `EllipticCurve/Reduction.lean:281` |
| moduli/Shimura/Hilbert; TateModule; arithmetic GaloisRep in Mathlib | **NONE FOUND** (FLT's own `GaloisRep` is the consumer type) | — |

Points over completions vs points over the global field are kept as distinct types
(`X.ptsOver K M_v` vs `X.ptsOver K L`) connected only by `ptsMap` along explicit continuous
algebra maps — no silent identification.

---

## 7. COUNTEREXAMPLES AND FAILURE MODES

- **CX-0 (topology as parameter — unsound axiom).** If `moret_bailly_point` quantified over an
  arbitrary `TopologicalSpace (X.ptsOver K M)` instance, instantiating with the discrete topology
  makes any singleton `{prescribed local point}` a nonempty open, and the axiom then asserts a
  global point specializing to an arbitrarily prescribed local point — false (X(L) is countable;
  a transcendental-coordinate point of X(K_v) is hit by no global point). The topology must be
  the canonical N1 definition. This is why INTERFACE-FIRST, not axiom-first.
- **CX-1 (independent local witnesses don't globalise).** Fields achieving each local condition
  separately cannot be composited: compositing L₁ (good at ℓ) with L₂ (good at p) can create
  ramification/complex places and destroys disjointness. The joint statement is the entire
  content of MB; any "split the theorem by place and recombine" architecture is rejected.
- **CX-2 (pairwise vs joint disjointness).** L = ℚ(√6) is linearly disjoint from ℚ(√2) and from
  ℚ(√3) but not from ℚ(√2,√3) ∋ √6. The avoidance input must be ONE compositum field
  (residual-kernel field ⊔ cyclotomic), never a list with pairwise disjointness. A3's `disjoint`
  field takes a single `Kavoid`.
- **CX-3 (Galois closure destroys disjointness).** ℚ(∛2) is linearly disjoint from ℚ(ζ₃)
  (degrees 3,2), but its Galois closure ℚ(∛2, ζ₃) contains ℚ(ζ₃). Hence if the exact source
  yields non-Galois L, "take the Galois closure" does NOT repair the design — C1 (Galois-ness)
  must be verified in the source text (SG-1) or the consumer chain redesigned. (Total splitting
  and total reality do survive Galois closure; disjointness does not.)
- **CX-4 (single-embedding conclusion too weak / ill-posed).** "P lands in Ω_v under SOME
  iso L_w ≅ M_v" differs by Gal(M_v/K_v) from other choices; without `galoisStable` the statement
  is ill-posed, and a some-w-only version is insufficient because good reduction of A is needed
  at EVERY prime above ℓ and p. The design states the ∀-w, ∀-e form with the invariance
  hypothesis, exactly as the blueprint does.
- **CX-5 (empty local open).** With some Ω_v = ∅ the conclusion is false. `nonempty` is an
  explicit hypothesis field; the hard local-solvability work (nonemptiness of the good-reduction
  locus of the moduli curve over K_v) stays a consumer obligation and is never absorbed.
- **CX-6 (splitting silently substituted for unramifiedness).** Risk R4, adjudicated by
  CONVERGENCE.md: the selected Taylor 2018 Thm 2.1.1 needs ℓ **unramified** in F (contract hyp 5)
  and the witness unramified at v|ℓ (hyp 7, the gpt56xhigh at-ℓ correction) — the
  complete-splitting demand belongs to the rejected Taylor 2006 Thm 3.3 route. Conversely,
  weakening the SOURCE's prescribed-extension conclusion to "unramified somewhere" is not
  source-faithful. Both directions are guarded: H7/C3 carry the exact prescribed extension; A1
  records `split ⇒ unramified` as a lemma with a proof, not a rename.
- **CX-7 (total reality / even degree asserted without construction).** Omitting archimedean
  prescriptions yields possibly-complex L (nothing in the finite-place data prevents it). Even
  degree is NOT an MB output — a design that adds `Even (finrank ℚ L)` to the axiom's conclusion
  strengthens the source and is rejected; A2 constructs it (real quadratic Q split at the two
  primes, jointly disjoint from L ⊔ Kavoid — joint, per CX-2 — with local conditions preserved
  because split primes leave completions unchanged).
- **CX-8 (solvability conflation).** `Assumptions/README.md` lists a *separate* class-field
  assumption "existence of a solvable extension with prescribed local behaviour". MB's L is
  Galois but in no way solvable, and no consumer in this route needs it to be; importing a
  solvability clause into MB (or citing MB for the solvable statement) is a category error.
- **CX-9 (circularity).** `exists_auxiliary_curve` must never be used to prove `nonempty` of an
  Ω_v (it is the output of the route). Nonemptiness comes from local moduli/CM constructions
  (FLT-CLASS-FIELD side). The dependency graph edge is one-directional (N5 → A4) and the control
  rows agree (FLT-MORET-BAILLY has no dependencies).
- **CX-10 (wrong points type).** Ω_v ⊆ X(K_v) but the point P ∈ X(L): membership only makes
  sense after `ptsMap` along the explicit completion embedding and the explicit iso e. Any
  design that quietly identifies X(L) with X(K_v), or uses Zariski opens (`X.Opens`) for Ω_v,
  fails soundness review.

---

## 8. FIRST BUILDABLE SLICE (kernel-clean, no axiom, no sorry)

File: `FLT/PotentialModularity/MoretBailly/LocalPoints.lean` (new; ~150–300 loc).
Imports: `Mathlib.AlgebraicGeometry.Over`, `Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.Topology.Algebra.Ring.Basic`, `Mathlib.Algebra.Algebra.Hom` (adjust to pinned paths).

Contents (N0 → N2 exactly):
1. `algHomTopology` + lemmas: `t2Space` (for Hausdorff R), continuity of precomposition
   `(A' →ₐ[K] A) → (A →ₐ[K] R) → (A' →ₐ[K] R)` and postcomposition along continuous algebra maps.
2. `Scheme.ptsOver` + `ptsOfAffine` + the canonical `TopologicalSpace` instance (final topology).
3. `ptsMap`, `continuous_ptsMap`, `ptsEquiv` (AlgEquiv action by homeomorphisms), functoriality
   `ptsMap (ψ.comp φ) = ptsMap ψ ∘ ptsMap φ`.

Also in the slice (independent, pure number theory): A1's
`unramifiedIn_of_splitsCompletely`-family in `FLT/PotentialModularity/AuxiliaryField.lean` **only
if** the spelling probe P7 lands cleanly; otherwise the slice is LocalPoints.lean alone.

Graph edges retired: N0→N1→N2 (all interface prerequisites of the N5 statement); flips
`library_matches` groundwork and makes the `lean_signature` probe for N5 runnable. Explicitly NOT
in the slice: the axiom (SG-1/SG-2), `AuxiliaryFieldCondition` freeze (SG-4), any moduli content
(SG-5). Verification: `lake build` of the new module; `#print axioms` on every new declaration
must show at most `[propext, Classical.choice, Quot.sound]`.

This is a true interface tranche (elaborated data/contracts), not a restatement of the desired
conclusion: nothing in the slice asserts existence of anything.

---

## 9. STOP-LOSS GATES

- **SG-1 (source gate — active now).** The MB 1989 text is not in the repository; the exact
  théorème number, the Galois-ness of L (C1), the disjointness clause (H2/C2), archimedean scope
  (H6), and the variety-class hypothesis (H5) are unverified. STOP before setting
  `hypothesis_translation` or admitting any axiom; operator must supply the paper (and, if the
  blueprint variant is a derived form, register the secondary derivation as an additional source
  next to SRC-011). Interface work (§8) proceeds regardless.
- **SG-2 (policy gate — active now).** `historical-assumptions.ndjson` `HIST-UNRESOLVED`: no T2
  assumption until exact Lean type + primary-source locator independently reviewed. Any attempt
  to add `axiom MoretBailly_statement` before that review is a hard stop.
- **SG-3 (elaboration gate).** If probes P1–P6 fail (universe mismatch in `Scheme.Over` at the
  needed universe, instance diamonds between `moduleTopology` and completion topologies,
  `Algebra (𝓞 K) (𝓞 L)` resolution for intermediate-field carriers), fall back in order:
  (a) abstract-field carrier `(L : Type u) [Field L] [Algebra K L]` with disjointness expressed
  via embeddings into Kbar; (b) affine-only X carrier with explicit coordinate ring. If both
  fail → escalate `OBSTRUCTION` to the operator.
- **SG-4 (vocabulary gate).** `AuxiliaryFieldCondition` (A3) must not be signature-frozen before
  the FLT-MLT-SOURCE coefficient/RACAR vocabulary is kernel-green (MLT-SOURCE-CONTRACT stop
  point); its deps row (`FLT-MLT-SOURCE, FLT-MORET-BAILLY`) enforces this. Do not guess MLT
  spellings.
- **SG-5 (consumer-shape gate).** The N5 statement is narrowed to relative dimension 1 (the
  blueprint's "curve"). If synthesis/Stage-2 finds the actual moduli object for
  (mod-ℓ ≅ ρ̄, mod-p induced) is not presentable as a smooth geometrically connected curve over
  the base (or its geometric connectedness fails for the twist), the axiom shape must be
  re-authorized (variety-level statement) — operator decision, since it strictly strengthens
  the assumed statement.

---

## 10. DEFINITION OF READY (maps to the seven SourceDesignStatus fields)

1. `primary_source_exact`: KEEP true only if upgraded to "text sighted": MB 1989 paper (I and II)
   in `methodology/evidence/sources/`, exact théorème number + page recorded in SOURCE-REGISTER
   with verification state "visually checked"; secondary derivation registered if the blueprint
   variant is derived. (Currently citation-level — SG-1.)
2. `hypothesis_translation`: table §3.1 completed with every UNVERIFIED mark resolved against the
   text; the at-∞ specialization decision (§11 Q3) recorded.
3. `proof_outline`: for T2, an admission outline (axiom + wrapper + registry row) AND a
   T3-feasibility sketch (MB's proof route: Picard groups / Skolem problems — recorded as
   research-level, estimates already in the control row); no outline may replace the text.
4. `sublemma_graph`: §4 graph with N0–N6, A1–A4, acyclic, gates attached; verified against the
   control rows' dependency edges.
5. `counterexample_review`: §7 CX-0…CX-10 reviewed by the independent reviewer; each mapped to
   the signature element that blocks it.
6. `library_matches`: §6 table re-probed after the first slice builds (per LIBRARY-SURVEY policy:
   "Every one must be re-searched after an exact statement is frozen").
7. `lean_signature`: N5 elaborates against pinned libs with `#print axioms` clean on the
   surrounding defs (the theorem itself absent until SG-1/SG-2); probes P1–P8 archived as
   evidence.

---

## 11. OPEN QUESTIONS FOR SYNTHESIS

- **Q1.** Obtain the MB 1989 text; confirm théorème number and whether the blueprint's
  prescribed-local-extension + linear-disjointness + Galois-L form is verbatim or derived (if
  derived, which secondary source to register — e.g. the standard potential-modularity
  restatement in the Taylor-school literature).
- **Q2.** Stage placement of a 1989 publication vs the `knownin1980s` pre-1990 scope: the control
  row itself says "T1 may use a named sourced historical boundary only if pre-1990 scope is
  accepted" — operator decision whether a T1 `knownin1980s` bridge is allowed while the T2 named
  axiom is being reviewed, or whether T2-only.
- **Q3.** Is the trivial-at-∞ (stay-real) specialization of the archimedean clause acceptable as
  the admitted axiom (weaker = safer, consumer-sufficient for K = ℚ), or should the general
  Galois L_v/ℝ form be admitted for reuse?
- **Q4.** Carrier choice ratification: `IntermediateField K Kbar` for L and Kavoid (my proposal,
  because disjointness and the kernel-field construction live there) vs abstract field carriers.
- **Q5.** Ownership of A2 (even-degree quadratic enlargement): a new small obligation under
  FLT-AUX-LOCAL-FIELD, or a deliverable of FLT-CLASS-FIELD (`classField_package` already owns
  "local prescriptions")?
- **Q6.** Universe discipline: FLT consumer types live at `Type u` with `Γ ℚ` over
  `AlgebraicClosure ℚ`; confirm `Scheme.{0}` vs `Scheme.{u}` for X so N5 and A4 compose without
  `ULift` noise (probe P1).
- **Q7.** Whether the eventual moduli curve will be handed to N5 with `[QuasiCompact]` (finite
  type) — if only locally of finite type, drop `QuasiCompact` from the axiom after checking the
  source's hypothesis (SG-1).

---

## Verification (for the executing agent)

Read-only design: no repo edits. To validate this design's claims: (1) re-run the greps cited in
§2/§6 at SHA 827eb96; (2) run probes P1–P8 as `#check` stubs in a scratch project pinned to the
same Mathlib rev; (3) build the §8 slice in a scratch copy and confirm `#print axioms` shows only
the standard trio; (4) confirm no file under `methodology/review/flt-completion/moret-bailly/`
other than the two prompt files was consulted (independence).

