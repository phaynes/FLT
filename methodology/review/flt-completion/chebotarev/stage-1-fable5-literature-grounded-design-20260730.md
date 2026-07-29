# Fable 5 literature-grounded Chebotarev design

- Model: claude-fable-5
- Invocation: fresh session, literature-grounded design prompt
- Duration: 1,455,677 ms
- Transport: success
- Terminal verdict: NO-RESULT (plan-mode response promised a later synthesis that did not arrive)
- Evidence use: retained as a static design, not an implementation approval
- Prompt: stage-1-literature-grounded-design-prompt-20260730.md

# FLT-CHEBOTAREV: literature-grounded design for the rank-two Chebotarev comparison

Hostile mathematical/Lean review deliverable. Repository read-only throughout.
Repo: `/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730`, design baseline
`8929b77` (HEAD `ba5504e` adds only the two design prompts). All types below verified first-hand
against the working tree and pinned Mathlib `a3364fae`.

## Context

`FLT-CHEBOTAREV` (proof-obligations.ndjson line 29) is `current_state: absent`,
`review_state: revision-required`, `target_stage: T2`, `completion_targets: [T2, T3]`,
`critical_path: true`, proposed declaration `FLT.CompatibleFamily.equal_of_charFrob_eq`, expected
module `FLT.GaloisRepresentation.CompatibleFamilyComparison`, source-design `dor: BLOCKED`,
`next_gate: "freeze the continuity and almost-all-Frobenius to all-elements theorem"`.
Its two in-edges are `FLT-COMPAT-DEF` (definition) and the freshly promoted `FLT-BRAUER-NESBITT`
(proved terminal `rankTwoContract`); its sole consumer is `FLT-COMPAT-CONTRA`.
Library-match `MISS-009`: no Chebotarev anywhere in pinned Mathlib (grep confirms: zero hits),
and zero `Chebotarev` occurrences in any repo `.lean` file.

The problem: `GaloisRepFamily.isCompatible` supplies charpoly data only at one **chosen** element
`adicArithFrob v` of each **local** group `Γ Kᵥ`, for `v` outside a finite `S` and away from the
residue characteristic; the proved Brauer–Nesbitt terminal demands charpoly equality on **every**
`g : Γ K`. The bridge is Chebotarev density plus deterministic topology/conjugacy/continuity
adapters. This design freezes that bridge as the smallest sound increment.

## 1. Verified repository facts the design stands on

- `GaloisRep K A M := letI := moduleTopology A (Module.End A M); Γ K →ₜ* Module.End A M`
  (FLT/Deformations/RepresentationTheory/GaloisRep.lean:49).
- `GaloisRep.toLocal ρ v = ρ.map (algebraMap K Kᵥ) = ρ.comp (Field.absoluteGaloisGroup.map _)`
  (GaloisRep.lean:309, 76) — so `ρ.toLocal v σ = ρ (Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) σ)`
  holds definitionally. **This is how local Frobenius reaches the global group**: contravariantly,
  via the continuous `Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) : Γ Kᵥ →ₜ* Γ K`
  (AbsoluteGaloisGroup.lean:96), which "relies on an arbitrarily chosen embedding of the algebraic
  closures". There is **no** global `Frob_v : Γ K` in the repo today.
- `Field.AbsoluteGaloisGroup.adicArithFrob v : Γ Kᵥ := arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ))`
  (AbsoluteGaloisGroup.lean:779); arithmetic normalization (`IsArithFrobAt` = `x ↦ x^q` on residue).
- `GaloisRep.charFrob_eq` (GaloisRep.lean:341): under `[ρ.IsUnramifiedAt v]` the charpoly at ANY
  arithmetic Frobenius lift agrees with `ρ.charFrob v` — lift-independence inside `Γ Kᵥ` is already
  proved; it is gated on unramifiedness (correctly: at ramified v the value is inertia-dependent).
- `GaloisRepFamily.isCompatible` (GaloisRepFamily.lean:58–64): `∃ S Pv, ∀ p φ v, v ∉ S →
  (p:𝓞 K) ∉ v.asIdeal → IsUnramifiedAt ∧ (toLocal v (Frob v)).charpoly = (Pv v).map φ`.
  (Monicity/degree of `Pv` live only in the docstring — noted as a latent contract gap, not
  load-bearing for this increment.)
- Proved terminal: `FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two`
  and `rankTwoContract` (RankTwo.lean:33, 71): arbitrary field, both semisimple, both finrank 2,
  charpoly equal on **all** g. Kernel-audited to `[propext, Classical.choice, Quot.sound]`
  (probe FLTMethodology/Probes/BrauerNesbittRankTwo.lean; evidence packet
  methodology/evidence/probes/FLT-BRAUER-NESBITT-RANK-TWO-20260730.md).
- Rank-two toolbox already banked: `LinearMap.charpoly_of_finrank_eq_two :
  f.charpoly = X² − C (trace f)·X + C (det f)` (AmitsurFinTwo.lean, no characteristic assumption);
  `trace_eq_of_charpoly_eq` (Contracts/BrauerNesbitt.lean:45).
- Continuity infrastructure: `GaloisRep.det : Γ K →ₜ* A` built from
  `IsModuleTopology.continuous_det` (GaloisRep.lean:202–204); Mathlib
  `IsModuleTopology.continuous_of_linearMap` (ModuleTopology.lean:340) for the trace.
- Topology of coefficients: `AlgebraicClosure ℚ_[p]` (= `PadicAlgCl p`) is a `NormedField` via the
  spectral norm (Mathlib NumberTheory/Padics/Complex.lean:67) ⇒ metric ⇒ `T2Space`, and a
  topological ring. `Continuous.ext_on` (Topology/Separation/Hausdorff.lean:508) needs T2 on the
  **codomain only**.
- `Representation.Equiv` (Mathlib RepresentationTheory/Equiv.lean),
  `Representation.IsSemisimpleRepresentation` (Semisimple.lean:34), `conjugatesOf`
  (Algebra/Group/Conj.lean:250), `LinearEquiv.charpoly_conj` (Charpoly/ToMatrix.lean:76),
  `Ideal.finite_factors` (DedekindDomain/Factorization.lean:85) all present in pinned Mathlib.
- Trace-only interfaces are REFUTED in-repo: `refutedOneSidedTraceContract_false`
  (FLTMethodology/Probes/BrauerNesbittBoundary.lean:290–338, ZMod 2 regression). The public
  interface must stay charpoly-valued.

## 2. Exact source-to-Lean hypothesis translation

Sources (quoted from the retrieved QMD files; the literature is *evidence for statement design*,
never a Lean proof):

**Gee 2022 (SRC-013, ~312–344).** §2.26: decomposition embedding `G_{K_v} ↪ G_K` "well-defined up
to conjugacy"; `[Frob_v] = {Frob_w}_{w|v}` a conjugacy class. Fact 2.27: for `K'/K` Galois
unramified outside finite `S`, "the union of the conjugacy classes `[Frob_v]`, `v ∉ S` is dense in
`Gal(K'/K)`". Remark 2.31: Chebotarev + Brauer–Nesbitt ⇒ each family member is determined by the
`charpoly(r_λ(Frob_v))`, `v ∉ S`.

| Source object | Lean translation | Status |
|---|---|---|
| embedding `G_{K_v} ↪ G_K` up to conjugacy | `Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) : Γ Kᵥ →ₜ* Γ K` (one chosen representative; injectivity never needed) | exists |
| `Frob_v` (arithmetic) up to inertia | `adicArithFrob v : Γ Kᵥ`; inertia-independence for charpoly = `charFrob_eq` under `IsUnramifiedAt` | exists |
| conjugacy class `[Frob_v]` in the global group | `conjugatesOf (globalAdicArithFrob v)` where `globalAdicArithFrob v := map (algebraMap K Kᵥ) (adicArithFrob v)` | NEW (D1, D3) |
| "union … dense in Gal(K'/K)" for every unramified-outside-S situation | `∀ T : Finset (Ω K), Dense (⋃ v ∉ T, conjugatesOf (globalAdicArithFrob v))` in the **full** `Γ K` | NEW contract (D4) — the number-theoretic authority, ASSUMED |
| Remark 2.31 consequence | `FLT.CompatibleFamily.equal_of_charFrob_eq` + `equiv_of_charFrob_eq` | NEW (T3, T4) |

**Taylor 2018 (SRC-016, ~680–690).** Dense-Frobenius trace comparison: from
`tr r(Frob_v) = tr r'(Frob_v)` a.e. and density of Frobenii in `G_S`, conclude `tr r = tr r'`,
"then `r ≅ r'` by semisimplicity". Divergences the design must not copy blindly:
(i) Taylor works in the quotient `G_S = Gal(F_S/F)` where Frobenius is honestly defined; the repo
has no `G_S` object, so the design states density in the full `Γ K` for *arbitrary lifts'*
conjugacy classes — a strictly stronger but still true statement (per finite quotient, discard the
finitely many ramified `v`, the rest restrict to genuine `Frob_w`); (ii) Taylor compares traces —
sufficient for char-0 semisimple reps but refuted as a general contract in-repo; the design carries
full charpoly equality through the interface and uses trace+det only *internally* in rank 2.

**Wiese (SRC-019, ~361–415).** Thm 1.2.8 finite Chebotarev (Dirichlet density `#[σ]/#G`);
Cor 1.2.9 and its proof: "in a profinite group `G` a subset `X ⊂ G` is dense iff the image of `X`
under all natural projections `G ↠ G_i` equals `G_i`". This is the *derivation route* for D4 at
T3, not part of the current increment: finite Chebotarev (analytic input, itself absent from
Mathlib) + profinite density criterion + `IsArithFrobAt` restriction compatibility. The design
records this decomposition so T3 work is scoped, but assumes only D4 now.

## 3. Authority separation (as demanded by the prompt)

1. **Number-theoretic density authority** — `ChebotarevFrobDensity K` (D4): a standalone `Prop`
   about `Γ K` and conjugacy classes of Frobenius lifts. It mentions **no representations, no
   charpolys, no comparison** — it cannot smuggle representation-theoretic content. Assumed
   (hypothesis-passed), never asserted as an axiom, never proved from literature.
2. **Deterministic adapters** — D1–D3, L1–L4 below: global image of local Frobenius, conjugacy
   invariance of charpoly along a representation, continuity of trace/det in the module topology,
   T2 dense-extension, finiteness of places over `p`. All provable now with standard axioms.
3. **Charpoly equality on all Galois elements** — T3′ (`equal_of_charFrob_eq`): consumes 1 + 2.
4. **Rank-two Brauer–Nesbitt terminal** — already proved (`rankTwoContract`); consumed as-is by
   T4′, with **no duplicated BN assumption** (completion-gate requirement).

## 4. Acyclic sublemma graph

```
D1 globalAdicArithFrob (def)                 ← adicArithFrob, absoluteGaloisGroup.map
D2 toLocal_apply_frob (rfl-lemma)            ← D1
D3 frobConjClassUnion (def)                  ← D1, conjugatesOf
D4 ChebotarevFrobDensity (Prop def; ASSUMED) ← D3          [number-theoretic authority]
L1 GaloisRep.charpoly_apply_conj             ← LinearEquiv.charpoly_conj
L2 GaloisRep.continuous_trace                ← IsModuleTopology.continuous_of_linearMap
L3 (exists) GaloisRep.det continuity         ← IsModuleTopology.continuous_det
L4 finite_setOf_mem_asIdeal (places ∣ p)     ← Ideal.finite_factors
T1' charpoly_eq_all_of_eqOn_dense (rank 2)   ← L2, L3, charpoly_of_finrank_eq_two,
                                               trace_eq_of_charpoly_eq, Continuous.ext_on
T2' charpoly_eqOn_frobConjClassUnion         ← D3, L1  (representatives ⇒ class union)
T3' FLT.CompatibleFamily.equal_of_charFrob_eq← D2, D4(hyp), L4, T1', T2'
T4' FLT.CompatibleFamily.equiv_of_charFrob_eq← T3', rankTwoContract, toRepresentation
T5' family wrapper (isCompatible ⇒ T3'/T4')  ← GaloisRepFamily.isCompatible, T3', T4'
P1 probe (#print axioms on all of the above) ← everything
```
No back-edges; D4 feeds forward only as an explicit hypothesis. Graph is acyclic by construction.

## 5. Candidate signatures

New module `FLT/GaloisRepresentation/CompatibleFamilyComparison.lean` (matches the node's
`expected_module`). Notation as in the repo: `Γ K`, `Ω K`, `Kᵥ`.

```lean
-- D1 (adapter: local Frobenius mapped into the global group, one chosen representative)
noncomputable def Field.AbsoluteGaloisGroup.globalAdicArithFrob
    {K : Type*} [Field K] [NumberField K] (v : Ω K) : Γ K :=
  Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) (adicArithFrob v)

-- D2 (rfl-level bridge; states the ONLY sense in which "ρ at Frob_v" is global data)
lemma GaloisRep.toLocal_adicArithFrob {ρ : GaloisRep K A M} (v : Ω K) :
    ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)
      = ρ (Field.AbsoluteGaloisGroup.globalAdicArithFrob v) := rfl

-- D3 (the dense set IS a union of conjugacy classes, not chosen elements)
def frobConjClassUnion (K : Type*) [Field K] [NumberField K] (T : Finset (Ω K)) : Set (Γ K) :=
  ⋃ v ∈ {v : Ω K | v ∉ T}, conjugatesOf (Field.AbsoluteGaloisGroup.globalAdicArithFrob v)

-- D4 (the number-theoretic authority; a named, typed, source-linked contract — never an axiom)
/-- Chebotarev-type density: after removing any finite set of places, the union of the global
conjugacy classes of the chosen arithmetic Frobenius lifts is dense in `Γ K`.
Sources: SRC-013 (Gee 2022) Fact 2.27; SRC-019 (Wiese) Thm 1.2.8 + Cor 1.2.9 (profinite
criterion). This contract is number-theoretic only: it mentions no representations. -/
def ChebotarevFrobDensity (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ T : Finset (Ω K), Dense (frobConjClassUnion K T)

-- L1 (conjugacy adapter: charpoly is a class function along any GaloisRep)
lemma GaloisRep.charpoly_apply_conj [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (h g : Γ K) :
    (ρ (h * g * h⁻¹)).charpoly = (ρ g).charpoly

-- L2 (continuity adapter; det analogue already exists as GaloisRep.det)
lemma GaloisRep.continuous_trace [IsTopologicalRing A] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : Continuous fun g : Γ K ↦ LinearMap.trace A M (ρ g)

-- L4 (finite exceptional places above the residue characteristic)
lemma HeightOneSpectrum.finite_setOf_natCast_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : {v : Ω K | (p : 𝓞 K) ∈ v.asIdeal}.Finite

-- T1' (dense agreement ⇒ agreement everywhere; T2 on the CODOMAIN only)
theorem GaloisRep.charpoly_eq_all_of_eqOn_dense
    {A : Type*} [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [Module.Finite A M] [Module.Free A M] [Module.Finite A N] [Module.Free A N]
    (hM : Module.finrank A M = 2) (hN : Module.finrank A N = 2)
    (ρ : GaloisRep K A M) (σ : GaloisRep K A N)
    {s : Set (Γ K)} (hs : Dense s)
    (hchar : ∀ g ∈ s, (ρ g).charpoly = (σ g).charpoly) :
    ∀ g : Γ K, (ρ g).charpoly = (σ g).charpoly

-- T2' (representatives suffice: class-union agreement from chosen-Frobenius agreement)
lemma GaloisRep.charpoly_eqOn_frobConjClassUnion … :
    (∀ v : Ω K, v ∉ T → (ρ (globalAdicArithFrob v)).charpoly = (σ (globalAdicArithFrob v)).charpoly)
    → ∀ g ∈ frobConjClassUnion K T, (ρ g).charpoly = (σ g).charpoly

-- T3' (THE NODE DECLARATION, name fixed by the obligation row)
theorem FLT.CompatibleFamily.equal_of_charFrob_eq
    {K : Type*} [Field K] [NumberField K]
    (hden : ChebotarevFrobDensity K)               -- density authority, explicit hypothesis
    {p : ℕ} [Fact p.Prime]
    (ρ σ : GaloisRep K (AlgebraicClosure ℚ_[p]) (Fin 2 → AlgebraicClosure ℚ_[p]))
    (T : Finset (Ω K))
    (hchar : ∀ v : Ω K, v ∉ T → (p : 𝓞 K) ∉ v.asIdeal →
      (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
      (σ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly) :
    ∀ g : Γ K, (ρ g).charpoly = (σ g).charpoly

-- T4' (terminal consumption; no duplicated Brauer–Nesbitt assumption)
theorem FLT.CompatibleFamily.equiv_of_charFrob_eq
    … same hypotheses as T3' plus
    (hss₁ : ρ.toRepresentation.IsSemisimpleRepresentation)
    (hss₂ : σ.toRepresentation.IsSemisimpleRepresentation) :
    Nonempty (Representation.Equiv ρ.toRepresentation σ.toRepresentation)

-- T5' (family wrapper over GaloisRepFamily ℚ E 2 members sharing compatibility data)
theorem GaloisRepFamily.charpoly_eq_all_of_shared_data
    {K E : Type*} … (ρ σ : GaloisRepFamily K E 2)
    (hden : ChebotarevFrobDensity K)
    (S : Finset (Ω K)) (Pv : Ω K → Polynomial E)
    (hρ : <isCompatible witness for ρ with data S, Pv>)
    (hσ : <isCompatible witness for σ with data S, Pv>) :
    ∀ {p} (hp : Fact p.Prime) (φ : E →+* AlgebraicClosure ℚ_[p]) (g : Γ K),
      ((ρ hp φ) g).charpoly = ((σ hp φ) g).charpoly
```

Notes. (a) `isCompatible` is existential; T5' therefore takes the *unpacked* shared witness
`(S, Pv)` — comparing two families whose witnesses merely exist would be unsound (different `Pv`).
(b) T3' does not require `IsUnramifiedAt`: it consumes charpoly equality at the chosen lifts
directly; unramifiedness only matters when a consumer wants lift-independence (`charFrob_eq`) or
`Pv`-matching, which is exactly what T5' extracts from `isCompatible`.
(c) T1' proof: `hchar` on `s` gives trace equality on `s` (`trace_eq_of_charpoly_eq`) and det
equality on `s` (constant coefficient via `charpoly_of_finrank_eq_two`); `Continuous.ext_on`
(codomain `A` is T2) upgrades both to all of `Γ K` using L2/L3; reconstruct charpolys with
`charpoly_of_finrank_eq_two` on both sides.

## 6. Explicit tests demanded by the prompt

**(i) Union of conjugacy classes vs chosen Frobenius elements.** The chosen-element set
`{globalAdicArithFrob v | v ∉ T}` is NOT provably dense and must not be the contract: three
stacked `Classical.choose`s (`arithFrobAt'`, the algebraic-closure embedding in
`absoluteGaloisGroup.map`, the valuation choice in `toLocal`) make the chosen set mathematically
uncontrolled — in a finite quotient with a nonabelian class (e.g. transpositions in an S₃
extension) the chosen lifts could, for all the axioms know, land on a single class member, and no
theorem forces them to sweep the class. Density is honestly a property of the **class union**
(Gee 2.27 is stated for class unions). The design encodes exactly that (D3/D4), and recovers
consumer-friendliness deterministically: charpoly is a class function along any representation
(L1), so agreement at representatives extends to the union (T2'). Conversely nothing in the
increment ever needs an element-level "Frobenius conjugacy transport" across places — which the
repo lacks (verified: no such lemma exists).

**(ii) Removal of finite exceptional places.** Two mechanisms compose:
- the contract D4 is quantified over **every** finite `T : Finset (Ω K)` — this is what makes the
  authority usable after enlarging the exceptional set (Chebotarev survives removing any finite
  set of places because each class arrives from infinitely many `v`);
- consumers enlarge `T` to `T ∪ {v | (p : 𝓞 K) ∈ v.asIdeal}` (finite by L4 via
  `Ideal.finite_factors`, since `(p) ≠ 0` in `𝓞 K` by characteristic zero), matching the
  `isCompatible` guard `(p : 𝓞 K) ∉ v.asIdeal`. At T3, the *derivation* of D4 additionally
  discards, per finite quotient, the finitely many `v` ramified in that quotient — a
  per-quotient, not global, removal; this is why D4 is true even though "Frob_v" is only a coset
  at ramified places.

**(iii) Mapping local Frobenius into the global group.** There is no subgroup-valued decomposition
embedding in the repo; the only bridge is `Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) :
Γ Kᵥ →ₜ* Γ K`, fixed by an arbitrary embedding of algebraic closures, and `toLocal` is
precomposition with it — so `ρ.toLocal v Frobᵥ = ρ (globalAdicArithFrob v)` by `rfl` (D2). The
choice-dependence is absorbed exactly by working with `conjugatesOf` in D3/D4 (a different
embedding choice conjugates the image, leaving the class union unchanged — this invariance is a
meta-observation motivating the statement, not a needed lemma).

## 7. Counterexample / normalization checks

1. **Trace-only interface refuted**: `refutedOneSidedTraceContract_false` (ZMod 2, 1⊕1⊕1 vs 3-dim)
   is banked in-repo. The public hypotheses and conclusions of T1'–T5' are charpoly-valued; traces
   and determinants appear only inside T1''s proof over the char-0 field `AlgebraicClosure ℚ_[p]`,
   where `charpoly_of_finrank_eq_two` reconstructs the full polynomial. No char-2 caveat: that
   lemma is characteristic-free.
2. **Arithmetic vs geometric normalization**: everything is pinned to `IsArithFrobAt` (`x ↦ x^q`).
   Both sides of every comparison use the same `adicArithFrob`; `Pv` in `isCompatible` is
   documented as arithmetic-Frobenius charpoly. No reciprocal-polynomial mixing is possible
   because no geometric Frobenius object exists in the repo.
3. **Ramified places**: `charFrob` is lift-independent only under `IsUnramifiedAt`
   (`charFrob_eq`); T5' takes unramifiedness from `isCompatible` and never evaluates at
   `v ∈ S ∪ {v ∣ p}`. T3' is agnostic (it uses whatever set `T` the consumer provides).
4. **Dense set really must live in `Γ K`**, not a `G_S` quotient: `GaloisRep` is a representation
   of the full `Γ K`; density in a quotient would only give charpoly equality on a subgroup's
   worth of cosets after unramifiedness arguments. D4 in full `Γ K` is the honest requirement, and
   is mathematically true for lift-class unions (per-quotient discard argument, Wiese Cor 1.2.9
   criterion). Documented as the T3 proof route.
5. **No hidden density**: D4's statement contains no `GaloisRep`, no `charpoly`, no `Module` —
   grep-checkably representation-free. T3' takes it as an explicit named hypothesis `hden`; no
   `axiom` command is introduced anywhere, so every new declaration audits to the standard trio.
6. **No duplicated Brauer–Nesbitt**: T4' invokes the proved `rankTwoContract` only; it takes no
   BN-shaped `Prop` hypothesis (completion-gate text requires exactly this).
7. **`Pv` monicity/degree gap**: `isCompatible` does not formalize the docstring's "monic degree
   d" claim. T5' does not need it (it only transports equalities of mapped polynomials), so the
   gap is noted but not load-bearing here; flagged for `FLT-COMPAT-DEF` owners.

## 8. T2 versus T3 axiom policy (governance meanings verified)

Per methodology/README.md:8–19, TRACEABILITY.md:55–61, and generate_graph.py targets:
T2 permits `["named historical assumptions", propext, Classical.choice, Quot.sound]` with the
generic `knownin1980s` axiom absent; T3 permits exactly the standard trio. Gates: G5 (T2
interface audit), G6 (T3 closure). Anti-laundering rule (TRACEABILITY.md:87–91): the same
obligation must remain load-bearing at T3 — no weaker second declaration.

Application:
- **All new Lean declarations in this increment are standard-trio now.** D4 is a `def … : Prop`
  (contributes no axioms); T3'/T4'/T5' consume it as an explicit hypothesis. `#print axioms` on
  every new theorem must report `[propext, Classical.choice, Quot.sound]` (P1 probe).
- **T2 exposure**: `ChebotarevFrobDensity K` joins the finite named historical-assumption
  interface (named, exactly typed, sourced to SRC-013/SRC-019; Chebotarev 1926 is comfortably
  inside the 1980s boundary). It must appear in the G5 interface audit as its own entry — not
  folded into any representation-comparison assumption.
- **T3 residue**: the SAME `ChebotarevFrobDensity K` must later be proved with standard-trio
  closure. Scoped decomposition recorded now: (a) finite Chebotarev for finite Galois extensions
  of number fields (analytic; absent from Mathlib; research-scale), (b) profinite density
  criterion (dense ⟺ surjective onto every finite quotient; elementary), (c) `IsArithFrobAt`
  restriction compatibility along `Γ K ↠ Gal(K'/K)` with per-quotient ramification discard
  (Mathlib `RingTheory/Frobenius` restriction API is the starting point). Same Prop at T2 and T3
  — anti-laundering satisfied.
- **Not T2-vs-T3 relevant but named for hygiene**: the topology usage needs only `T2Space` on the
  coefficient field (satisfied by the spectral-norm metric); no `T3Space`/regularity instance is
  ever required (`Continuous.ext_on` demands T2 on the codomain only, nothing on `Γ K`).

## 9. Smallest vertical slice worth implementing now

Everything in §5 **except** any attempt at proving D4, plus the probe:

1. `FLT/GaloisRepresentation/CompatibleFamilyComparison.lean`: D1, D2, D3, D4 (def only), L1, L2,
   L4, T1', T2', T3', T4', T5'. Estimated 250–450 LOC total; the only genuinely risky lemma is
   T1' (module-topology continuity plumbing).
   - Fallback for L2/T1' if `Module.End`-level continuity fights the `letI` module topology:
     specialize to `M = Fin 2 → A` and route through `FramedGaloisRep.GL` + matrix-entry
     continuity + `Continuous.matrix_det`/`Matrix.trace` (Mathlib Topology/Instances/Matrix.lean)
     — the node only needs the framed case.
2. `FLTMethodology/Probes/ChebotarevComparison.lean`: `#print axioms` on all of T1'–T5'
   (expected: standard trio each) — the promotion evidence surface, mirroring the BN probe.
3. Control-plane (separate commit, BN-promotion precedent): update the `FLT-CHEBOTAREV` row
   (`current_state: absent → admitted`-with-named-interface or per-governance wording;
   `kernel_probe_state` per probe result), add a **new obligation node** for the density contract
   (suggested `FLT-CHEBOTAREV-DENSITY`, `target_stage: T2`, `completion_targets: [T2, T3]`,
   `lean_declaration: ChebotarevFrobDensity`, sources SRC-013/SRC-019, edge
   `FLT-CHEBOTAREV-DENSITY → FLT-CHEBOTAREV`), regenerate `proof-graph.ndjson` via the fail-closed
   generator, and run the promotion review gate. A separate node is what keeps the density theorem
   visible at G5 instead of hidden inside the comparison node.

Out of scope, explicitly not claimed: any proof of `ChebotarevFrobDensity` (Chebotarev itself),
`FLT-COMPAT-CONTRA`, general-dimension `Contract`, FLT completion.

## 10. Verification

- `lake build FLT FLTMethodology` must stay green (BN rereview baseline: 9,043 jobs).
- P1 probe: `#print axioms` = `[propext, Classical.choice, Quot.sound]` for every new theorem;
  any `sorryAx` or new axiom fails closed.
- Generator replay: `python3 methodology/control/generate_graph.py` must reproduce byte-identical
  derived files after the control-plane edit (56 obligations / 103 edges expected if the density
  node is added); cycles fail closed.
- Negative checks: grep the new module for `axiom` (must be absent); confirm D4's def references
  no `GaloisRep`/`Representation`/`charpoly` symbol.
- Independent re-review gate per BN precedent before any `review_state` change.
