# INDEPENDENT FABLE 5 DIVERSITY DESIGN — CLASS-FIELD RESIDUAL (`FLT-CLASS-FIELD`)

**Role:** Stage-5 hostile independent designer (Fable ladder, diversity slot).
**Mode:** read-only; no repository files edited; all Lean checks run via `lake env lean --stdin`
against the working tree (Lean `4.32.0-rc1` toolchain pin, Mathlib `a3364fae…`).
**Scope:** only the four residual uncertainties left open by Stage-4's REVISE. The two rank-one
carrier predicates are accepted as-is (independently re-verified below), per the Stage-5 prompt.

**Verdict: `DESIGN-VIABLE`** — for the interface/object layer, with the reciprocity *theorems*
correctly held as definition-gaps behind explicit gates. Justification in §8.

---

## Context

Stages 1–4 converged on: carrier predicates `IsFiniteOrderCharacter` / `HasPrescribedLocalComponents`
elaborate (after `open NumberField`) with the standard axiom trio; Skinner–Wiles and induced-rep
bookkeeping routed out; reciprocity held at definition-gap. Stage-4 left four residuals: (i)
ownership/direction of the reciprocity → inertia → residue-field chain; (ii) the normalization the
actual MLT/S-good consumers use; (iii) the honest finite-idele vs idele-class-topology boundary;
(iv) the exact T2-nameability partition. This report resolves all four from repository evidence and
live Lean elaboration, and identifies two facts every prior stage got wrong or missed (§0).

## 0. New facts no prior stage established

**0.1 The class-field component already has LIVE Lean consumers — the ledger's "no consumers" is
stale.** Repo-wide grep for `localTameAbelianInertiaGroup` finds four consuming declarations:

| Consumer | Locator | Use |
|---|---|---|
| `FLT.ModularityLifting.BlueprintSGood.traceOnJ` | `FLT/ModularityLifting/Conditions.lean:40` | `∀ σ ∈ localTameAbelianInertiaGroup v, LinearMap.trace R V (rho.toLocal v σ) = 2` |
| `traceConditionFunctor` | `FLT/Deformations/LiftFunctor.lean:127–134` | same trace-2 condition, `Fin 2` framed |
| `narrowTraceConditionFunctor` | `FLT/Deformations/LiftFunctor.lean:137–144` | trace-2 on full `localInertiaGroup v` |
| `cyclic_base_change` (hypothesis `hρtame`) | `FLT/GaloisRepresentation/Automorphic.lean:186` | `localTameAbelianInertiaGroup w ≤ δ.ker` for a rank-one `δ : GaloisRep (w.adicCompletion F) (ℚ_[p]ᵃˡᵍ) (ℚ_[p]ᵃˡᵍ)` |

Stage-1 asserted "Actual Lean consumers of FLT-CLASS-FIELD: NONE"; Stages 2–4 exposed the
source/graph mismatch only as blueprint prose (`ch04overview.tex:44–60`). In fact the mismatch is
**consumer-visible in compiled Lean**: the proof-graph edges (`proof-graph.ndjson`
`E-CLASS-FIELD-INDUCED-MOD`, `E-CLASS-FIELD-AUX-CURVE`) route class-field only to two *absent*
declarations, while the *existing* consumers are MLT-side. Also note `cyclic_base_change`'s `δ` has
exactly the `GaloisRep Kᵥ A A` rank-one carrier shape of the Stage-3 predicates — independent
confirmation that the carrier choice is the right vocabulary.

**0.2 The idele-class OBJECT is nameable today; the "missing domain object" claim is half-wrong.**
Verified by direct Lean elaboration this session (§4): the full multiplicative idele group
`(NumberField.AdeleRing (𝓞 K) K)ˣ` is already a topological commutative group in pinned Mathlib
(instances `Units.instCommGroupUnits`, `Units.instTopologicalSpaceUnits`,
`Units.instIsTopologicalGroupOfContinuousMul` all fire — Mathlib's `Units` topology is the induced
topology from `M × Mᵐᵒᵖ`, which IS the correct idele topology, evading the
`IsOpenUnits.lean:22` subspace-topology trap), and the quotient by multiplicative principal ideles
elaborates with `CommGroup` (`QuotientGroup.Quotient.commGroup`) and `IsTopologicalGroup` instances,
axiom closure = standard trio. What is genuinely missing is: the **group structure on π₀** (concrete
instance-diamond, §4.3), and every **theorem** about these objects (§4.4). All four prior stages
classified the object itself as absent; that misdirects the next build slice.

---

## 1. Residual (i): ownership and direction of reciprocity → inertia → residue-field

**Ownership: elementary ramification theory, NOT local reciprocity.** The blueprint says so
explicitly — "Local class field theory **(or a more elementary approach)** gives a map
`I_v → 𝒪_{F_v}^×` and hence `I_v → k(v)^×`" (`ch04overview.tex:46–47`) — and the repository has
already committed to the elementary route: `localTameAbelianInertiaGroup`
(`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:178`) defines the **kernel**
directly via the Kummer fixed-field trick (`Kᵘʳ((q−1)-th root of ϖ)`, docstring notes all units of
`Kᵘʳ` have `(q−1)`-th roots), with `TODO: show that this is indeed the right group`
(`AbsoluteGaloisGroup.lean:176`).

Consequences (correcting Stage-1's DAG, sharpening Stage-3/4):

- The node owning `I_v → k(v)ˣ` (here `T-TAME-RESIDUE`) must have **no dependency edge from
  `CF-LOCAL-RECIP`**. Stage-1's arrow (local reciprocity ⟶ derived inertia map) is backwards for
  this repository.
- The full local iso `Kᵥˣ ≃ₜ* (W_{Kᵥ})ᵃᵇ` is **off the MLT critical path entirely**: no live
  consumer touches it; its only future consumer is compatibility bookkeeping inside
  `FLT-INDUCED-MOD`. Hold at lowest priority.
- Stage-4's demand ("state the derivation `I_K → W_Kᵃᵇ → Kˣ`, prove image in `𝒪ˣ`, reduce to
  `k(v)ˣ`") describes the CFT-side *compatibility theorem*, not the consumer-required map. It is a
  later obligation of `T-LOCAL-RECIP`, not a gate on `T-TAME-RESIDUE`.

**Direction: consumer-invisible today; pin it as a recorded convention, not a theorem gate.** All
four live consumers use the subgroup only through membership (`σ ∈ …`, trace condition) or
`≤ δ.ker` — every one is invariant under inverting the tame character (a character and its inverse
have identical kernels; `trace = 2` on a *subgroup* is inversion-stable). There is **no observable
in the current repository that distinguishes `σ ↦ σ(x)/x` from `σ ↦ x/σ(x)`.** Pin the standard
tame character
`t_v(σ) = (σ x)/x mod 𝔪`, for `x` a `(q−1)`-th root of a uniformizer, `q = Nat.card (κ 𝒪ᵥ)`
(well-defined independent of the choices of `x` and ϖ because units of `Kᵘʳ` have `(q−1)`-th roots
in `Kᵘʳ`), target `κ(v)ˣ` via `μ_{q−1}(Kᵘʳ) ≅ κ(v)ˣ`. Record — do not yet formalize — that under the
arithmetic-normalized local Artin map this corresponds to the unit projection `𝒪ᵥˣ → κ(v)ˣ`.

**Target signature (definition-gap, constructible now with medium Kummer-API effort; owns the
in-repo TODO):**

```lean
-- T-TAME-RESIDUE (definition gap; elementary, no CFT input)
-- noncomputable def tameResidueChar (v : Ω K) : (localInertiaGroup v) →* (κ 𝒪ᵥ)ˣ
-- theorem localTameAbelianInertiaGroup_eq_ker_tameResidueChar (v : Ω K) :
--     localTameAbelianInertiaGroup v = (tameResidueChar v).ker.map (localInertiaGroup v).subtype
--   -- discharges the TODO at AbsoluteGaloisGroup.lean:176
-- (stateable-now warm-up lemma, no new defs required:)
-- theorem localTameAbelianInertiaGroup_le_localInertiaGroup (v : Ω K) :
--     localTameAbelianInertiaGroup v ≤ localInertiaGroup v
--   -- proof route: σ fixes fixedField (localInertiaGroup v) pointwise, then infinite Galois
--   -- correspondence; requires closedness of the inertia subgroup — flagged, not assumed.
```

Source locator to register for the kernel theorem: Serre, *Corps Locaux* / *Local Fields* (GTM 67),
Ch. IV §2 (tame quotient of inertia, `I/I_wild ≅ ∏_{ℓ≠p} ℤ_ℓ(1)`, first-layer quotient `≅ μ_{q−1}`).
Chapter-level is given here; the T2 gate (§5) requires the register to fix the exact
proposition number before any assumption is named.

## 2. Residual (ii): normalization used by the actual MLT/S-good consumers

The S-good conditions themselves (`BlueprintSGood`, `traceConditionFunctor`) are
**normalization-free** (§1). The binding normalization lives one level up, in the automorphic
matching that any future reciprocity statement must not contradict:

- `GaloisRep.IsAutomorphicOfLevel` (`FLT/GaloisRepresentation/Automorphic.lean:70–101`) pins
  **arithmetic Frobenius**: `Frob := Field.AbsoluteGaloisGroup.adicArithFrob` with
  `det (ρ.toLocal v (Frob v)) = v.1.absNorm` ("det(ρ) = cyclo", i.e. cyclotomic character evaluates
  to `N(v)` on *arithmetic* Frobenius) and
  `trace (ρ.toLocal v (Frob v)) = π(Tᵥ)` (Hecke eigenvalue). Charpoly of arithmetic Frobenius is
  `X² − aᵥX + N(v)`.
- `GaloisRep.charFrob` (`GaloisRep.lean:335`) and `BlueprintSGood.det`
  (`Conditions.lean:37–38`, cyclotomic determinant) use the same objects.

**Therefore: the repository-coherent convention is the arithmetic normalization — the global/local
Artin maps must send a local uniformizer to (the coset of) an arithmetic Frobenius.** The blueprint
offers both (`chtopbestiary.tex:83`: "one sends local uniformisers to arithmetic Frobenii and the
other to geometric"); the repo's automorphic side has already chosen. Stage-3's formula
("arithmetic Artin map, uniformizer ↦ **geometric** Frobenius") is internally inconsistent, as
Stage-4 flagged; the resolution is: **uniformizer ↦ arithmetic Frobenius**, matching `adicArithFrob`.
Counterexample if violated: with geometric normalization, the idele-class character corresponding to
`det ρ = cyclo` sends the class of `localUniformiserUnit v` to `N(v)⁻¹`, contradicting the
`IsAutomorphicOfLevel` clause `det ρ(Frobᵥ) = N(v)` at every good place — a sign error detectable at
the very first compatibility lemma.

The uniformizer-side vocabulary already exists: `FiniteAdeleRing.localUniformiserUnit`
(`FLT/DedekindDomain/FiniteAdeleRing/LocalUnits.lean:76–96`), and the Frobenius-side coset is
expressible now: image of `adicArithFrob v` under
`Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) : Γ Kᵥ →ₜ* Γ K`
(`AbsoluteGaloisGroup.lean:75`) into `Field.absoluteGaloisGroupAbelianization K`
(Mathlib `FieldTheory/AbsoluteGaloisGroup.lean:59`), **modulo the image of `localInertiaGroup v`**
(the Frobenius class in `Γᵃᵇ` is only well-defined mod inertia image — any future
`T-GLOBAL-RECIP` clause must be stated as a coset condition, not an equality of elements).

## 3. Residual (iii): honest boundary — finite-idele infrastructure vs idele-class topology

Layered inventory, each line verified this session against the pinned tree:

| Layer | Status | Evidence |
|---|---|---|
| Finite adeles + topology | EXISTS | `IsDedekindDomain.FiniteAdeleRing` (Mathlib) |
| Finite-idele units, restricted-product form | EXISTS | `RestrictedProduct.unitsEquiv` (Mathlib `Topology/Algebra/RestrictedProduct/Units.lean:24`) — **a `MulEquiv` only; its homeomorphism upgrade is missing** |
| `Kˣ → (FiniteAdeleRing R K)ˣ` | EXISTS | `FiniteAdeleRing.unitEmbedding` (Mathlib `RingTheory/DedekindDomain/FiniteAdeleRing.lean:178`) |
| Local uniformizer ideles | EXISTS | `localUniformiserUnit`, `localUnit` (`FLT/DedekindDomain/FiniteAdeleRing/LocalUnits.lean`) |
| Full adele ring (arch. included) | EXISTS | `NumberField.AdeleRing` (Mathlib `NumberTheory/NumberField/AdeleRing.lean:47`; `principalSubgroup` :70 is additive-only) |
| **Idele group as topological comm. group** | **EXISTS (new finding)** | `#synth` fires: `Units.instCommGroupUnits`, `Units.instTopologicalSpaceUnits`, `Units.instIsTopologicalGroupOfContinuousMul` on `(AdeleRing (𝓞 K) K)ˣ`. Mathlib's `Units` topology (embedding into `M × Mᵐᵒᵖ`) is the correct idele topology; the `IsOpenUnits.lean:22` warning rules out only the naive subspace topology, which nobody needs |
| **Idele class group object** | **NAMEABLE NOW (new finding)** | `principalIdeles` + `IdeleClassGroup` elaborate; `CommGroup` and `IsTopologicalGroup` instances verified; axiom trio (§4) |
| π₀ type | NAMEABLE NOW | `ConnectedComponents.instTopologicalSpace` fires; type elaborates, axiom trio |
| **π₀ group structure** | **BLOCKED — instance plumbing, not mathematics** | exact failure recorded in §4.3 |
| `Kˣ` discrete/closed in ideles | MISSING THEOREM | needs archimedean product-formula bridges (Stage-4 was right *for this theorem*, wrong for the object) |
| Idele topology ≅ restricted product of local units | MISSING THEOREM | upgrade of `unitsEquiv` to homeo + archimedean factor |
| Compactness / profiniteness of π₀, norm-one compactness | MISSING THEOREMS | nothing in pinned Mathlib |
| Reciprocity map | MISSING (definition + theorem) | no `artinMap` anywhere; external repos (`mariainesdff/LocalClassFieldTheory`, `kbuzzard/ClassFieldTheory`) cited only in Mathlib comments |

**Boundary statement:** everything up to and including the idele-class *object* and π₀ *type* is
buildable now with zero axioms; everything from "`Kˣ` is discrete" onward is missing *mathematics*
(not merely missing names) and stays behind stop-loss S1. The Stage-3 phrase "cokernel of
`unitEmbedding` is the missing idele class group" must be rejected — see counterexample CE-6.

## 4. Lean-verified probe results (run this session, `lake env lean --stdin`)

### 4.1 Carrier predicates (Stage-3/4 text, independently reproduced)

`IsFiniteOrderCharacter`, `HasPrescribedLocalComponents` — exact Stage-4 block with
`import FLT.Deformations.RepresentationTheory.GaloisRep` + `open NumberField`:
both elaborate; `#print axioms` = `[propext, Classical.choice, Quot.sound]` for both. Confirms the
Stage-4 elaboration report byte-for-byte. (Also re-confirmed: without `open NumberField`, `𝓞` is
not in scope — the module-scoped `open NumberField` at `GaloisRep.lean:26` does not export.)

### 4.2 Idele-class objects (NEW; all axiom-trio, no sorryAx)

```lean
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Multiplicative principal ideles. (The additive `AdeleRing.principalSubgroup` is unusable here.) -/
noncomputable def principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range

/-- The idele class group as a topological commutative group. -/
noncomputable def IdeleClassGroup := (AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K
-- VERIFIED: #synth CommGroup ((AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K)
--   ⇒ QuotientGroup.Quotient.commGroup (principalIdeles K)
-- VERIFIED: example : IsTopologicalGroup ((AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K) := inferInstance
-- VERIFIED: #print axioms ⇒ [propext, Classical.choice, Quot.sound]
```

### 4.3 π₀ — exact blocking record (so the next slice doesn't rediscover it)

`Subgroup.connectedComponentOfOne` exists (Mathlib `Topology/Algebra/Group/Basic.lean:741`) and the
quotient **type** `IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)`
elaborates (axiom trio). But its group structure does not synthesize in the pinned Mathlib:

- `#synth Monoid (ConnectedComponents (IdeleClassGroup K))` — **fails** (no algebraic instances on
  `ConnectedComponents` of a topological group anywhere in pinned Mathlib).
- Quotient route: `CommGroup (IdeleClassGroup K ⧸ connectedComponentOfOne …)` — **fails**:
  needs `(connectedComponentOfOne …).Normal` ⇐ `Subgroup.normal_of_isMulCommutative` ⇐
  `IsMulCommutative (IdeleClassGroup K)`, which does not synthesize; the manual fix `⟨⟨mul_comm⟩⟩`
  hits a `Mul`-diamond (`QuotientGroup.Quotient.group` vs `CommMagma.toMul` heads).

This is **typeclass plumbing** (a dedicated file defining `IdeleClassGroup` with explicitly
registered `CommGroup`/`IsMulCommutative`/`Normal` instances, or a small Mathlib upstream), not
mathematics. It is excluded from the no-axiom slice below and gated as P3.

### 4.4 What 4.2 does NOT prove

Object nameability only. No claim that `Kˣ` is discrete, that the quotient is Hausdorff/locally
compact, that π₀ is profinite, or any reciprocity. A π₀ statement over a possibly-non-Hausdorff
quotient is semantically premature until `principalIdeles` is proved closed (T-DISCRETE, missing,
archimedean input required).

## 5. Residual (iv): T2-nameability partition

Policy: `historical-assumptions.ndjson:1` — no T2 assumption until **exact Lean type AND
primary-source locator** are independently reviewed. `SRC-004` is "explicitly incomplete"
(`SOURCE-REGISTER.md:12`); `[cf]` is book-level with no theorem/page locator; the register (SRC-001…017)
contains **no CFT source**. Hence:

| Interface | Type today | Source locator today | Class |
|---|---|---|---|
| `IsFiniteOrderCharacter`, `HasPrescribedLocalComponents` | exact, verified | n/a — kernel-clean **definitions**, not assumptions | **bankable now** |
| `principalIdeles`, `IdeleClassGroup` (+ instances) | exact, verified | n/a — definitions | **bankable now** |
| π₀ group object | type verified; instances blocked | n/a — definition | after P3 plumbing |
| `tameResidueChar` + kernel theorem (T-TAME-RESIDUE) | constructible, not yet written | Serre, *Local Fields*, Ch. IV §2 — register entry required | **not T2-nameable yet**; first theorem gap to close (owns in-repo TODO) |
| `T-GLOBAL-RECIP` (π₀ ≃ₜ* Γᵃᵇ + ϖ↦Frob-mod-inertia clause + local compat) | type-complete **after** P3 + T-DISCRETE; clause vocabulary exists (`localUniformiserUnit`, `adicArithFrob`, `absoluteGaloisGroup.map`, `absoluteGaloisGroupAbelianization`) | Cassels–Fröhlich Ch. VII (Tate) — exact theorem/§ must be fixed at register time | **not T2-nameable** (both gates open) |
| `T-LOCAL-RECIP` (`Kᵥˣ ≃ₜ* (W_{Kᵥ})ᵃᵇ`) | NOT stateable — Weil group absent (`chtopbestiary.tex:19` is `\notready` prose) | Cassels–Fröhlich Ch. VI (Serre) — unregistered | **not nameable; off critical path — hold** |
| `T-CHAR-GLOBALIZE` (Grunwald–Wang) | not honestly stateable (non-exceptionality vocabulary absent) | Artin–Tate, *Class Field Theory*, Ch. X — unregistered | **not nameable**; first sound sub-target: **odd-order characters** (unconditionally non-exceptional), which discharges stop-loss S3 by scope restriction |
| `Skinner_Wiles_CFT_trick` | — | `\uses` of `modularity_lifting_theorem` (`ch04overview.tex:68`), not of any CF node | **routed OUT** → `FLT-AUX-LOCAL-FIELD` |
| `det/cond(Ind χ)` bookkeeping | — | — | **routed OUT** → `FLT-INDUCED-MOD` |

No `CF-*` node references `IsAutomorphicOfLevel`, auxiliary-curve existence, automorphy, or any
omnibus authority axiom (checked against every signature in this report — circularity guard holds).

## 6. Minimal component DAG

```
P1  CF-CHAR predicates ................................ VERIFIED, unbanked (probe file absent)
P2  CF-IDELE-OBJ (principalIdeles, IdeleClassGroup) .... VERIFIED, unbanked   [defs only]
P3  π₀ instance plumbing ............................... BLOCKED-PLUMBING (§4.3)
T1  T-TAME-RESIDUE: tameResidueChar + kernel theorem ... DEFINITION-GAP (elementary; NO CFT edge)
      └─ discharges TODO @ AbsoluteGaloisGroup.lean:176
      └─ semantic backing for live consumers: BlueprintSGood.traceOnJ,
         traceConditionFunctor, narrowTraceConditionFunctor, cyclic_base_change.hρtame
T2a T-DISCRETE: principalIdeles discrete/closed ........ MISSING MATH (archimedean bridges)
T2b T-GLOBAL-RECIP statement ........................... gated on {P3, T2a, source-register entry, T2 review}
      └─► future consumers: FLT-INDUCED-MOD, FLT-AUX-CURVE (per proof-graph.ndjson:88,91)
T3  T-CHAR-GLOBALIZE (odd-order first) ................. gated on T2b
HOLD T-LOCAL-RECIP (Weil group) ........................ off critical path; no current consumer
OUT Skinner_Wiles_CFT_trick → FLT-AUX-LOCAL-FIELD ;  det/cond(Ind) → FLT-INDUCED-MOD
```

Edges deliberately ABSENT: `T-LOCAL-RECIP → T1` (see §1); any edge into automorphy/curve nodes.
**Ledger correction required (not executed):** add the class-field → MLT consumer relationship
(the live trace-condition consumers) to the proof graph; correct `library_candidates`
(`IsLocalClassField`, `ContinuousCharacter` do not exist in Mathlib `a3364fae…`); add a CFT source
row (Cassels–Fröhlich; Serre *Local Fields*; Artin–Tate) to `SOURCE-REGISTER.md`.

## 7. Counterexamples (statement-risk register)

- **CE-1 (degenerate carrier, retained):** `A = ZMod 1` — `[Nontrivial A]` mandatory; verified
  present in the carriers.
- **CE-2 (Grunwald–Wang, retained & sharpened):** over ℚ there is no cyclic degree-8 extension with
  local degree 8 at 2 (equivalently, 16 is an 8th power in every `ℚ_p`, p odd, and in ℝ, but not in
  ℚ). Unconditional prescribed-local-components existence is **false**; the first formal target must
  be the odd-order sub-case, with the exceptional set made explicit only when the 2-primary theory
  is actually built.
- **CE-3 (normalization):** geometric-normalized reciprocity forces `det ρ(Frobᵥ) = N(v)⁻¹` against
  `IsAutomorphicOfLevel`'s `= N(v)` (§2). Arithmetic normalization is pinned by existing code, not
  by taste.
- **CE-4 (Frobenius coset):** `rec(class of localUniformiserUnit v) = image of adicArithFrob v` as an
  *element* equality in `Γᵃᵇ` is ill-posed — well-defined only modulo the image of
  `localInertiaGroup v`. Any T-GLOBAL-RECIP clause must be a coset/`mod`-statement.
- **CE-5 (idele topology):** with the `𝔸`-subspace topology, inversion is discontinuous
  (Mathlib `IsOpenUnits.lean:22` names `𝔸ₖ` a non-example); sequences converging adelically to 1 with
  inverses escaping. Mathlib's `Units` embedding topology — which is what 4.2 uses — is the correct
  one; no bespoke topology may be introduced.
- **CE-6 (archimedean loss — kills the finite-idele shortcut):** for `K = ℚ`,
  `coker(FiniteAdeleRing.unitEmbedding) ≅ Ẑˣ/{±1}`, whereas `π₀(𝔸_ℚˣ/ℚˣ) ≅ Ẑˣ ≅ Gal(ℚᵃᵇ/ℚ)`.
  The finite-idele cokernel loses exactly complex conjugation — i.e. the parity (odd/even) of
  characters — which `FLT-INDUCED-MOD` converse-theorem matching needs. Stage-3's identification
  "cokernel of `unitEmbedding` = missing idele class group" is **wrong**, not merely incomplete.
- **CE-7 (direction, new):** no current consumer distinguishes `t_v` from `t_v⁻¹` (§1); therefore any
  review demand to "derive the direction first" gates nothing that compiles today — direction is a
  recorded convention until `T-LOCAL-RECIP` compatibility exists.
- **CE-8 (π₀ over non-Hausdorff quotient):** if `principalIdeles` were not closed, the quotient is
  non-Hausdorff and `ConnectedComponents` conclusions are semantically fragile; T2a precedes any
  π₀ *theorem* (object definitions are unaffected).

## 8. Verdict and next no-axiom build slice

**Verdict: `DESIGN-VIABLE`.** The four residuals are resolved with repository evidence: (i)
tame-residue chain owned by elementary ramification theory, direction consumer-invisible, local
reciprocity off critical path; (ii) arithmetic-Frobenius normalization forced by
`IsAutomorphicOfLevel`; (iii) boundary moved — idele-class *objects* nameable now (Lean-verified),
theorems from `Kˣ`-discreteness onward remain honest gaps; (iv) exact T2 partition in §5 with the
two blocked gates (source-register locator, domain objects) named per item. No authority axioms; no
node hides Skinner–Wiles, induction bookkeeping, or automorphy. `DECOMPOSE-FIRST` is not warranted —
the decomposition is complete and every piece is either verified, gated, or routed out;
`OBSTRUCTION` is not warranted — nothing consumed by live code is unsound or unreachable.

**Next no-axiom build slice** (single probe file, mirrors `Probes/MLTSourceBoundary.lean`
conventions; not created in this read-only pass — `FLTMethodology/Probes/` confirmed to contain no
ClassField probe):

`FLTMethodology/Probes/ClassFieldCharacterBoundary.lean`, registered in `FLTMethodology.lean`:

```lean
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient

open NumberField

namespace FLT.PotentialModularity.ClassField

def IsFiniteOrderCharacter
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv

variable (K : Type*) [Field K] [NumberField K]

noncomputable def principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range

noncomputable def IdeleClassGroup := (AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
#print axioms FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
#print axioms FLT.PotentialModularity.ClassField.principalIdeles
#print axioms FLT.PotentialModularity.ClassField.IdeleClassGroup
```

Build/pass gate:

```
lake build FLTMethodology.Probes.ClassFieldCharacterBoundary
```

every `#print axioms` = `{propext, Classical.choice, Quot.sound}`, no `sorryAx`. All four bodies
were elaborated verbatim through Lean stdin this session with exactly that closure. π₀ is
**deliberately excluded** (§4.3 blocking record); it enters the following slice together with its
explicit instance registrations, and no theorem about any of these objects is claimed by the probe.

**Stop-losses (inherited, re-scoped):** S1 — if `Kˣ`-discreteness/idele-restricted-product bridges
don't land in the wave, T2b stays a named gap; keep P1/P2/T1 only. S2 — any reappearance of
Skinner–Wiles/induction bookkeeping inside a CF node ⇒ REVISE. S3 — discharged by scope-restriction
(odd-order first). S4 — solvable-field work stays in `FLT-AUX-LOCAL-FIELD`.

*Nothing in this report edits the repository, registers an axiom, or promotes an obligation.
Interface elaboration is not mathematical proof.*
