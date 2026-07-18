# Opus 4.8 Post-Diversity Synthesis — Cyclic Base Change (`FLT-CBASE`)

**Actor:** Opus-4.8 post-diversity synthesizer, difficulty 10. **Mode:** read-only; no repository
files, task state, source rows, obligations, or generated graphs edited. All Lean evidence obtained by
disposable `lake env lean --stdin` probes (nothing written to the repo).
**Repository:** `/Volumes/second-store/devel/proof-forks/FLT`, toolchain `leanprover/lean4:v4.32.0-rc1`.
**Inputs read in full:** stage-1 (Opus48 primary), stage-2 (GPT-5.6 xhigh review), stage-3 (Fable-5
diversity repair), `FLT/GaloisRepresentation/Automorphic.lean:1–194`, the cited GaloisRep / Hecke /
quaternion / place-transport / frozen-probe APIs, and the control rows + edges for FLT-CBASE,
FLT-AUT-DEF, FLT-JL, FLT-CLASS-FIELD, FLT-MLT, FLT-BRAUER-FAMILY.

## Verdict

# READY-FOR-GPT-REVIEW

Carrying sub-verdict **`INTERFACE-FIRST, TWO-BOUNDARIES-OPEN`**. This authorizes **only** an independent
GPT agreement review. It authorizes **no** build, **no** graph mutation, **no** T2 registration, and
**no** FLT-CBASE promotion. FLT-CBASE stays `admitted`; the two analytic boundaries stay source-open.

---

## Context — why this synthesis exists

`cyclic_base_change` (`Automorphic.lean:137`, body `sorry` at `:194`) is the sole `sorryAx`-only leak
in the clean import surface, pinned by `ExistingAdaptersAudit.lean:116`; graph row `FLT-CBASE` is
`admitted`, `target_stage: T2`, `direct_dependencies: [FLT-AUT-DEF]`, consumed by `FLT-MLT`
(`E-CBASE-MLT`, theorem edge) and `FLT-BRAUER-FAMILY` (`E-CBASE-BRAUER-FAMILY`, theorem edge). Three
prior agents diverged: Opus (READY, but with a non-elaborating D1, `sorry`-scaffolds under `FLT/`, and
an over-strong reading of the predicate), GPT-5.6 (REVISE, Fable-trigger YES), Fable-5 (DESIGN-VIABLE,
fixed D1, added B3, surfaced the universe and total-definiteness defects). This synthesis reconciles
them into the smallest source-faithful, dependency-ordered architecture, re-probed against the kernel.

All eight buildable declarations below were re-probed **today** and audit to **exactly**
`[propext, Classical.choice, Quot.sound]`. No production `sorry`, custom axiom, `unsafe`, or
`native_decide` is proposed anywhere.

---

## 1. Two-universe admitted theorem vs single-universe tensor route (Req 1)

**Kernel-confirmed fact (probe P0).** `@cyclic_base_change` binds `{F : Type u_1}` and `{E : Type u_2}`
in **independent** universes; `@GaloisRep.IsAutomorphicOfLevel` binds its witness `∃ (D : Type u)` at
the *field's* universe (`Automorphic.lean:84`). Applied to the `E`-side, the RHS existential demands a
witness `D_E : Type u_2`. The only in-tree base-change construction is `E ⊗[F] D : Type (max u_1 u_2)`
(instance `IsQuaternionAlgebra E (E ⊗[F] D)`, `Automorphic.lean:99`). `max u_1 u_2 = u_2` is **not**
derivable for unconstrained universes ⇒ **no forward-transfer proof can instantiate the RHS via the
tensor route** without ULifting the whole quaternion/Hecke/automorphic-form stack. This is a
type-theoretic obstruction that *precedes* every mathematical provider (confirms & sharpens GPT
defect 6 and Fable R1).

**Scope reconciliation.** Both graph consumers instantiate at **concrete number fields in `Type 0`**:
`FLT-MLT` (`FLT.ModularityLifting.Main`) and `FLT-BRAUER-FAMILY` (`FLT.GaloisRepresentation.CompatibleFamily`)
work over concrete `F, E`. At `Type 0`, `max 0 0 = 0 = u_2` holds definitionally, and `E ⊗[F] D : Type 0`.
Exhaustive grep confirms (Opus §1) **no live Lean consumer** of `cyclic_base_change` exists — every
reference is a `#check`/`#print axioms` probe or a contract/quarantine audit. **Therefore the theorem's
downstream value is fully recovered by a single-universe statement at the concrete consumers with zero
scope loss.** The two-universe generality is exactly — and only — the part that is unprovable by the
tensor route.

**Exact operator decision (needed only if the public statement changes).** Two admissible dispositions:

- **(A) Keep the two-universe public type.** Then any future T3 proof must either ULift the entire
  quaternion/Hecke/automorphic stack to `Type (max u_1 u_2)` or supply a non-tensor witness construction.
  This is a large, currently-unbudgeted cost and trips stop-loss **G4** (no `ULift` transport of the
  quaternion/Hecke stack). Recommended posture: forbid the ULift route; leave the theorem admitted.
- **(B) Re-freeze `cyclic_base_change` at a single universe `u` for `F, E, D`.** Loses nothing at any
  instantiation (no live consumer; all consumers are `Type 0`), and makes the tensor route type-check.
  But it **mutates a frozen admitted public declaration and its `FLT-CBASE` graph row** — a public-type
  change. That is an **operator decision**, not a designer action, and must not be taken in this pass.

**Synthesis recommendation:** state every *new* interface (§4) at a **single universe `u`** — safe,
lossless, no public-type change. Record option (B) as a deferred FLT-CBASE statement decision for the
operator; do **not** mutate the admitted theorem now. Until the operator rules, the two-universe
statement is recorded as *unprovable-by-tensor-route* (not disproved).

---

## 2. `IsAutomorphicOfLevel` total-definiteness / even-degree gap = FLT-AUT-DEF risk (Req 2)

**Source-confirmed (read `Automorphic.lean:84–88`).** The existential requires only `DivisionRing D`,
`Algebra F D`, `IsQuaternionAlgebra F D`, `IsQuaternionAlgebra.NumberField.WithRigidification F D`. The
class `IsQuaternionAlgebra.IsTotallyDefinite` **exists** (`FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean:143`)
but is **not** a hypothesis of the predicate, of `WeightTwoAutomorphicForm`, or of `HeckeAlgebra`; the
docstring's "totally definite" is **unenforced**. The predicate also carries no `Even (finrank ℚ F)`
side-condition. Over a field with ≥ 4 real places a discriminant-1 division algebra can be indefinite
(ramified at a proper even subset of infinite places), so the witness ranges over form spaces with no
classical automorphic meaning and no finiteness theorem (Fable R2, corroborated).

**Disposition.** This is a **statement risk of `FLT-AUT-DEF`** (row currently `current_state: proved`,
`review_state: unreviewed`, `lean_risk: high`, `source_condition_risks: "Must match the automorphy
notion used by the selected lifting theorem"`), **not** of FLT-CBASE. It is a **soundness risk wherever
`IsAutomorphicOfLevel` appears as a hypothesis** — i.e. at `FLT-MLT`/`FLT-HECKE-ACTION`. **Do not exploit
the weaker predicate.** Stop-loss gate **G-AUT** below fails any CBASE route that instantiates the
automorphy witness with a non-totally-definite `D` or that drops even-degree reasoning. Escalate R2 to
FLT-AUT-DEF as a named statement-risk review item; propose no repository edit in this pass.

---

## 3. Smallest immediate T3 build slice — frozen (Req 3, 7)

Four declarations, all **re-probed today → exactly the standard trio**. Landing site (build pass only,
separately authorized): **one new methodology probe file** `FLTMethodology/Probes/CyclicBaseChangeBoundary.lean`
(outside the verified `FLT/` root — per `methodology/README.md` probes are not proof progress; FLT-CBASE
stays `admitted`). B2a/B2b/B3 are additionally upstream-PR-able into `FLT/DedekindDomain/IntegralClosure.lean`
and `.../HeckeOperators/Concrete.lean` in a later build-authorized pass.

| ID | Declaration | Content | Probe |
|----|-------------|---------|-------|
| **B1** | `even_finrank_of_even_base` | `Even (finrank ℚ F) → Even (finrank ℚ E)` via `Module.finrank_mul_finrank` + `hF.mul_right`. GPT-corrected form (`NumberField` instances synthesize `Module ℚ _`; Opus's `FiniteDimensional`-only form fails `failed to synthesize Module ℚ F`). | trio ✓ |
| **B2a** | `mem_preimageComapFinset_iff` | `w ∈ preimageComapFinset … S ↔ w.under (𝓞 F) ∈ S`. | trio ✓ |
| **B2b** | `natCast_notMem_of_mem_preimageComapFinset` | good-place transport `(p:𝓞 F)∉v → (p:𝓞 E)∉w` for `w` above `S`. | trio ✓ |
| **B3** | `heckeAlgebra_algHom_ext` | **Q-empty Hecke eigensystem rigidity**: for `𝒮.Q = ∅`, two `R`-algebra homs `HeckeAlgebra D 𝒮 →ₐ A` agreeing on all good `T_v` are equal, by `Algebra.adjoin_induction`. | trio ✓ |

**B3 is NOT multiplicity one — keep it distinct (Req 3).** The `cyclic_base_change` level data is
`⟨Fact.out, S, ∅, 1, by simp, hp⟩`, i.e. Taylor–Wiles set `Q = ∅`, so `HeckeAlgebra D 𝒮` is generated
by the good operators `T_v` alone (`Concrete.lean:874`; the `U`-generators are indexed by `v ∈ 𝒮.Q = ∅`).
B3 says an *eigensystem* is pinned by its good-place values. **Multiplicity one is a statement about
*forms*** (the eigenspace of a pinned eigensystem is one-dimensional / a form with those eigenvalues
exists on a specific `D`) and is **not statable** with the pinned API (no automorphic-representation
vocabulary; `library-matches.ndjson:MISS-006`). B3 cleanly demarcates the provable eigensystem half
from the missing form half, repairing Opus's C4-vs-descent conflation. Stop-loss **G7** fails any
presentation of B3 as multiplicity one.

Build gate: `lake build FLTMethodology.Probes.CyclicBaseChangeBoundary` + per-declaration
`#print axioms` = the trio (all four already observed today).

---

## 4. Complete elaborating interface signatures, dependency order (Req 4, 7)

All **single-universe `u`** (§1). All re-probed today → the trio (V3/V4 emit only the unused-binder
lints the admitted theorem itself suppresses via `set_option linter.unusedVariables false`). Flat/tame
bundles **reuse the frozen probe vocabulary** `FLTMethodology.SelectedGoodBoundary.HasFlatDescentAboveEll`
/ `HasGenericTameRankOneQuotient` (verbatim `hρflat`/`hρtame`) — no duplicate vocabulary.

Dependency order (each uses only items above it + the pinned API):

- **V1 `IsTwistBy (rho' rho : GaloisRep K A M) (chi : GaloisRep K A A) : Prop`** — relational twist,
  `∀ g m, rho' g m = chi g 1 • rho g m`. No smuggled continuity obligation (a *constructed*
  `GaloisRep.twist` with its continuity proof is deferred, not needed to state anything downstream).
- **V2 `FactorsThroughGal (F E) … (chi : GaloisRep F A M) : Prop`** — invariant-character vocabulary,
  `∀ g : absoluteGaloisGroup E, chi (absoluteGaloisGroup.map (algebraMap F E) g) = 1`. Requires
  `[NumberField F] [NumberField E]` (discovered by probe: `absoluteGaloisGroup.map` needs them).
- **V5 `BaseChangeFiberUpToTwist (rho sigma : GaloisRep F A M) : Prop`** — Galois-side base-change fiber
  ("descends up to twist"): if `rho`, `sigma` become conjugate over `E`, they differ over `F` by a
  `Gal(E/F)`-factoring twist. **Statable now, T3-provable in principle** (finite-index Clifford/Schur
  theory, **no analytic input**). This splits GPT-defect-2's "image characterization" into an
  **algebraic fiber statement (V5 — future T3 residual, no source needed)** and an **analytic
  surjectivity-onto-invariants statement (form-level, not statable with the pinned API — owned jointly
  with FLT-AUT-DEF/FLT-JL)**. Only the latter needs a Langlands-type source. Opus's D5 hid both.
- **V6/V7/V9 local transports (implication-shaped `Prop`s)** — the non-thin remainder of "D2" that
  `preimageComapFinset` does *not* supply: `TameQuotientTransport`, `UnramifiedTransport`,
  `DetCyclotomicTransport` (det = cyclotomic under restriction, `F`→`E` closures).
- **V8 `FrobeniusCharpolyTransport (rho) (w : HeightOneSpectrum (𝓞 E)) : Prop`** — local Frobenius
  compatibility at `w | v`, stated on **characteristic polynomials** (not endomorphisms) because
  `GaloisRep.map` and `adicArithFrob` each make documented arbitrary choices (Fable R3): transport is
  only well-posed up to conjugacy. Uses `w.asIdeal.inertiaDeg (𝓞 F)` (pinned spelling; naive
  `p.inertiaDeg P` fails, discovered by probe).
- **Q1 `BaseChangeUnitsProvider (F E D : Type u) … : Prop`** — `∀ a : E ⊗[F] D, a ≠ 0 → IsUnit a`, i.e.
  `E ⊗[F] D` is a division ring. Stated on `IsUnit` (compatible with the tensor ring structure and the
  pinned dichotomy `nomepty_algEquiv_matrix_or_forall_isUnit`), not `Nonempty (DivisionRing _)`.
- **Q2 `BaseChangeRigidificationProvider (F E D) … : Prop`** —
  `Nonempty (WithRigidification E (E ⊗[F] D))`. Data construction (engineering, not source-blocked).
- **V3 `ForwardSolvableBaseChange (…full binder list…) : Prop`** — `F`-automorphic ⟹ `E`-automorphic at
  the pulled-back level (`ASSUME-CBASE-FORWARD`).
- **V4 `SolvableBaseChangeDescent (…identical binder list…) : Prop`** — the reverse implication
  (`ASSUME-CBASE-DESCENT`).

**`hρirred` preserved conservatively on BOTH directions (Req 4).** Kept as a hypothesis of V3 and V4.
*Forward:* the only classical route to the quaternionic `E`-conclusion is JL⁻¹ ∘ (GL₂ base change) ∘ JL;
the re-descent to the totally-definite side requires the base change to be **cuspidal**, which fails
exactly when `ρ|G_E` is induced from an intermediate extension — precisely what `hρirred` excludes
(on the repository's Galois-side packaging, reducible `ρ|G_E` gives norm-form-character eigensystems no
in-tree fact rules out). *Descent:* `hρirred` is the standard "not induced" precondition for image
characterization. **Decision rule:** no registered source resolves whether forward can drop it; Opus's
counterexample-3 claim ("using `hρirred` in D4 signals a mis-split") is **unsourced hypothesis-minimization
and is rejected** until an operator registers and visually verifies a primary source whose forward
statement is hypothesis-free. Conservative both-sides placement loses no downstream strength: both graph
consumers carry irreducibility at their call sites (`proof-obligations.ndjson:15,24`). `hF, hS, hρdet,
hρflat, hρunram, hρtame` are likewise retained globally (the admitted theorem quantifies them globally;
no source licenses per-direction splitting yet). The admitted `cyclic_base_change` equals
`∀ …, ForwardSolvableBaseChange … ∧ SolvableBaseChangeDescent …` modulo the single-universe restriction
and the flat/tame repackaging — consumer scope (`E-CBASE-MLT`, `E-CBASE-BRAUER-FAMILY`) preserved.

---

## 5. Provider taxonomy — T3-provable vs the two analytic T2 boundaries (Req 5)

**T3-provable now (algebraic/engineering; no historical source):**
`B1, B2a, B2b, B3` (built today); then, in residual order — `V5` (Clifford-theoretic, algebraic),
`V9` (cyclotomic-character functoriality), `Q2` (engineering over
`FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv`, `.../BaseChange.lean:351`), `V8` at unramified `w`
(Frobenius functoriality), `V6/V7` (local Galois functoriality). **`Q1` is T3-eligible only after
`FLT-CLASS-FIELD` provides Hasse–Brauer–Noether local–global input** — it is *not* CBASE-owned.

**Two analytic T2 source boundaries — SOURCE GATE OPEN, NOT AUTHORIZED (Req 5):**
`ASSUME-CBASE-FORWARD ≙ V3` and `ASSUME-CBASE-DESCENT ≙ V4`. **No T2 assumption is proposed as
authorized.** `SOURCE-REGISTER.md` has **no** primary base-change row (only `SRC-004`, the explicitly
incomplete blueprint chapter `ch04overview.tex`). **The base-change, Jacquet–Langlands, and
strong-multiplicity-one source locators remain visually unverified**: Langlands is cited *by name only*
(`KnownIn1980s.lean`, `blog.md:39` — author "only the most superficial understanding of"); Arthur–Clozel
has **zero** in-tree occurrences; JL is a named open obligation (`FLT-JL`, `current_state: absent`,
`target_stage: T2`) with no locator. Any artifact citing Langlands/Arthur–Clozel by theorem number
before registration is **citing from memory → reject** (gate G-SRC). Candidate sources the operator must
obtain, register, and *visually verify* before **any** authorization — named **without** page/theorem
locators (which would be fabrication): Langlands' cyclic base-change monograph for GL(2); Arthur–Clozel
*Simple Algebras and Base Change*; a Jacquet–Langlands source and a strong-multiplicity-one source for
inner forms of GL(2) over totally real fields; a Skinner–Wiles solvable-iteration packaging source. What
must be visually verified: printed hypotheses cover (i) totally real solvable `E/F`, (ii) quaternionic
(not bare GL₂) packaging or an explicit JL bridge, (iii) `U₁(S)`/conductor behaviour under base change,
(iv) the cuspidality condition governing `hρirred` (§4).

---

## 6. Acyclic owner graph, gates, first residual Lean goals (Req 6)

```
FLT-AUT-DEF  (proved row; IsAutomorphicOfLevel; carries R2 total-definiteness statement-risk)
   │  E-AUT-DEF-CBASE (definition edge)
   ▼
FLT-CBASE  (admitted; direct_dependencies = [FLT-AUT-DEF] only)
   ├─▶ CBASE-L0 : {B1,B2a,B2b,B3}                     [T3 now; probe-verified trio]        owner FLT-CBASE
   ├─▶ CBASE-VOCAB : {V1,V2,V5,V6,V7,V8,V9,Q1,Q2,V3,V4 as defs}  [probe-verified trio]     owner FLT-CBASE
   │       ├─▶ CBASE-GAL-FIBER : prove V5           (algebraic T3 residual; no source)
   │       ├─▶ QUAT-BC : prove Q2 ; then Q1 ◀── FLT-CLASS-FIELD (Hasse–Brauer–Noether)
   │       ├─▶ LOCAL-TRANSPORT : prove V6,V7,V8,V9  (reachable functoriality)
   │       ├─▶ ASSUME-CBASE-FORWARD (≙V3)  T2 ; operator gate ; SOURCE GATE OPEN
   │       └─▶ ASSUME-CBASE-DESCENT (≙V4)  T2 ; operator gate ; SOURCE GATE OPEN ;
   │                 form-level image / mult-one / JL vocabulary ◀── FLT-JL, FLT-AUT-DEF
   └─▶ cyclic_base_change  (admitted; later = ⟨V3-inst, V4-inst⟩ ; scope preserved)
          ├─▶ E-CBASE-MLT (theorem)          ▶ FLT-MLT (absent)
          └─▶ E-CBASE-BRAUER-FAMILY (theorem) ▶ FLT-BRAUER-FAMILY (absent; +C6 coefficient
                                                 transport, BRAUER-owned, out of the iff)
```

**Acyclic by construction (Req 6).** No CBASE node consumes `FLT-MLT`, `FLT-POTMOD`, or any
potential-automorphy output. Confirmed against the rows: `FLT-POTMOD` depends on `FLT-MLT`
(`E-MLT-POTMOD`); `FLT-MLT` depends on `FLT-CBASE` (`E-CBASE-MLT`); `FLT-BRAUER-FAMILY` depends on
`FLT-POTMOD` and `FLT-CBASE`. Therefore **any CBASE→MLT/POTMOD dependence would close a cycle → reject
(gate G5)**. `FLT-JL` (absent, T2) feeds **descent vocabulary only** (form-level image/mult-one); it is a
sibling, not a CBASE ancestor. `C6` coefficient/semisimplification transport is **BRAUER-owned** and stays
**out** of the CBASE iff (both sides share `V` and `A = ℚ_[p]ᵃˡᵍ` via `ρ.map`, so no coefficient transport
is needed *inside* CBASE) — all three prior artifacts agree.

**Completion gates.** CBASE-L0 + CBASE-VOCAB: `lake build` + `#print axioms` = trio (met today).
CBASE-GAL-FIBER/LOCAL-TRANSPORT/QUAT-BC: kernel-clean T3 proofs, trio audit. ASSUME-CBASE-FORWARD/DESCENT:
require a registered, visually-verified primary source **and** operator T2 authorization through the human
agreement gate; only then is `cyclic_base_change` recomposed as `⟨V3-inst, V4-inst⟩` with no scope loss.
`FLT-CBASE` row's own `completion_gate` ("Forward transfer and the exact descent/image theorem required
by MLT have acceptable target-stage axiom closure") is satisfied only when both boundaries are either
proved (T3) or T2-registered-and-authorized.

**First residual Lean goals, in strict order (each precedes Hecke-eigensystem transport).**
1. **Universe reconciliation (R1)** — type-theoretic; blocks the tensor route at elaboration. Resolved by
   the single-universe interfaces here, or by operator re-freeze option (B) (§1).
2. **`DivisionRing (E ⊗[F] D)` = `BaseChangeUnitsProvider` (Q1)** — first genuinely *mathematical* missing
   provider. True under the formal hypotheses (`D` division + rigidified ⇒ ramified only at infinite
   places; `E` totally real keeps them real; nonempty ramification ⇒ division), but the proof *is*
   Hasse–Brauer–Noether local–global theory: absent from tree, owned by FLT-CLASS-FIELD-adjacent work.
   The pinned dichotomy lemma only says "matrix algebra or division"; it cannot decide which.
3. **`WithRigidification E (E ⊗[F] D)` = `Q2`** — data construction; support exists
   (`baseChangeAdeleContinuousAlgEquiv`, `mapRingHom`) but no adapter connects it to `M₂(𝔸ᶠ[E])`;
   engineering-heavy, not source-blocked.
4. **`U₁Data` transport + Frobenius compatibility** — assemble `⟨Fact.out, S_E, ∅, 1, by simp, hpE⟩` from
   B2a/B2b + `hpE`; then `V8` with **inert-degree Satake bookkeeping**: the `E`-side eigenvalue at `w | v`
   of residue degree `f` is a polynomial in the `F`-side `T_v`-eigenvalue and `N(v)` (e.g. `t_w = t_v² −
   2·N(v)` for `f = 2`) — an algebra-hom `T_w ↦ polynomial(T_v, N(v))`, **not** `T_w ↦ T_v` as Opus's
   "transport the Hecke system" implied.
5. Only then the analytic core (V3/V4 content proper) — the named T2 boundary.

---

## 7. Stop-loss gates (halt and report OBSTRUCTION if any trips)

- **G1 (hidden axiom):** a proposed proof of V4 (or the iff) that does not consume form-level
  image / mult-one / JL vocabulary — hidden-axiom smell.
- **G2 (audit purity):** any production declaration with replacement `sorry`, custom axiom, `unsafe`, or
  `native_decide` in the CBASE tranche. (Opus's plan to land D3–D5 as `sorry` bodies under
  `FLT/GaloisRepresentation/BaseChange/Structural.lean` is **rejected** — it would mint new `sorryAx`
  production declarations, violating `IMPLEMENTATION-PLAN.md:126ff`; GPT defect 3.)
- **G-AUT (R2):** any route that exploits the total-definiteness gap (instantiating the automorphy witness
  with a non-totally-definite `D`) or drops even-degree reasoning — escalate to FLT-AUT-DEF, do not proceed.
- **G4 (universe):** any provider requiring `ULift` transport of the quaternion/Hecke stack — halt; restate
  at one universe, or route to operator decision (B).
- **G5 (cycle):** any dependence of a CBASE node on FLT-MLT / FLT-POTMOD / potential automorphy.
- **G6 (axiom drift):** axiom audit of any landed declaration differing from exactly
  `[propext, Classical.choice, Quot.sound]`.
- **G7 (statement integrity):** B3 (eigensystem rigidity) presented anywhere as multiplicity one.
- **G-SRC:** any T2 authorization before a primary base-change/JL/mult-one source row exists in
  `SOURCE-REGISTER.md` with visual verification of §5 items (i)–(iv); any citation by theorem number
  before registration.

---

## 8. Probe log (all disposable `lake env lean --stdin`; nothing written to repo)

| # | Declaration(s) | Result |
|---|----------------|--------|
| P0 | `#check @cyclic_base_change`, `@GaloisRep.IsAutomorphicOfLevel` | two independent universes `u_1`,`u_2`; witness `D : Type u` at field universe — **R1 confirmed** |
| P1 | B1 `even_finrank_of_even_base` (GPT-corrected) | **trio** `[propext, Classical.choice, Quot.sound]` |
| P2 | B2a `mem_preimageComapFinset_iff`, B2b `natCast_notMem_of_mem_preimageComapFinset` | both **trio** |
| P3 | B3 `heckeAlgebra_algHom_ext` (`Q = ∅`) | **trio** |
| P4 | V1 `IsTwistBy`, V2 `FactorsThroughGal`, V5 `BaseChangeFiberUpToTwist`, V8 `FrobeniusCharpolyTransport` | all **trio** |
| P5 | Q1 `BaseChangeUnitsProvider`, Q2 `BaseChangeRigidificationProvider`, V3 `ForwardSolvableBaseChange`, V4 `SolvableBaseChangeDescent` | all **trio** (V3/V4 unused-binder lints only) |

Every claimed buildable declaration passed a probe; none is reported without one. Oleans were prebuilt
(`FLT.GaloisRepresentation.Automorphic`, `FLTMethodology.Probes.SelectedGoodRepositoryBoundary`); no
build was triggered against the repo and no file was written.

---

## 9. What a positive verdict does and does not authorize

READY-FOR-GPT-REVIEW authorizes **only** an independent GPT agreement review of this synthesis.
It does **not** authorize: creating `FLTMethodology/Probes/CyclicBaseChangeBoundary.lean`; any edit to
`FLT/`; any control-row/graph mutation (no FLT-CBASE state change, no new nodes/edges); T2 registration of
`ASSUME-CBASE-FORWARD`/`ASSUME-CBASE-DESCENT`; or FLT-CBASE promotion. `FLT-CBASE` remains `admitted`,
quarantined by `ExistingAdaptersAudit.lean:116`; both analytic boundaries remain source-open; no historical
assumption is authorized. The fail-closed monitor (`methodology/control/flt_monitor.py`) remains the
promotion authority; this artifact is advisory.

## Verification (for the separately-authorized build pass, if later approved)

1. Create `FLTMethodology/Probes/CyclicBaseChangeBoundary.lean` with §3 (proved B1–B3) + §4 (V1–V9,Q1,Q2
   as `def`s), importing `FLT.GaloisRepresentation.Automorphic` and
   `FLTMethodology.Probes.SelectedGoodRepositoryBoundary`; `lake build` it; record `#print axioms` = trio
   on every declaration.
2. No `FLT/` edits, no control-row mutation, except as the operator separately authorizes: optional
   upstream-PR of B2a/B2b/B3; an FLT-AUT-DEF review item for R2 and a universe decision for R1;
   `SOURCE-REGISTER.md` rows for base-change/JL/mult-one **after** visual check.
3. T2 authorization of the two boundaries only after (2c), through the human agreement gate; then recompose
   `cyclic_base_change` as `⟨V3-inst, V4-inst⟩` with no scope loss.
