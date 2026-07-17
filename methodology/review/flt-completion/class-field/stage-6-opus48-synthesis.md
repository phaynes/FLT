# Stage 6 Opus 4.8 synthesis — class field

## Model and transport evidence

- Agent: `opus48-primary-designer-d10`
- Configured model: `claude-opus-4-8`
- Backend transport: Claude CLI through `kg_model_bridge`
- Role: post-Fable synthesis producer
- Design budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `439.412 s`
- Baseline HEAD: `7d4243260c35941b3fc1543001635f6b3c472645`
- Claude session: `716b79f6-3af9-42c4-856f-92c65105c59e`
- Prompt: `methodology/review/flt-completion/class-field/stage-6-prompt-opus48-synthesis.md`
- Verdict: `READY-FOR-GPT-REVIEW`
- Repository mutation authority: read-only; no model edits permitted

## Complete synthesis

# FLT-CLASS-FIELD — Opus 4.8 Synthesis (Stage 6, difficulty 10)

**Component:** `class-field / FLT-CLASS-FIELD`
**Role:** non-scarce Opus synthesis producer, read-only. No repo/control/git edits; no axiom
registered; no obligation promoted; no production Lean built.
**Verdict: `READY-FOR-GPT-REVIEW`.**

---

## Context — why this synthesis exists

Stage 1 (Opus) proposed an omnibus `classField_package` with a 4-way split; Stage 2 (GPT-5.6 xhigh)
returned a correct **REVISE**; Stage 3 (Opus repair) narrowed to a source-faithful split and banked
the two carrier predicates; Stage 4 (GPT-5.6) returned **REVISE** on residual reciprocity/idele
issues; Stage 5 (Fable-5 diversity) returned **DESIGN-VIABLE** and established two facts no earlier
stage had: the component **already has live compiled MLT consumers**, and the **idele-class object is
nameable today**. This synthesis fuses those into one exact design, preserving the Stage-5
corrections (all five re-verified first-hand against the frozen tree below), and hands GPT-5.6 a
single reviewable interface set with an axiom-clean build slice.

**Frozen tree:** Lean `v4.32.0-rc1`, Mathlib `a3364fa…`. Every path/line below was read directly
this session (not taken on a prior stage's word). FLT oleans are **not** cached, so the live probe is
deferred to the build slice (a fresh stdin probe would transitively compile FLT = a production build,
which is out of scope); the two carrier predicates were already stdin-elaborated by **both** Stage 4
and Stage 5 with identical axiom closure, and the idele objects by Stage 5.

---

## 1. Single exact Lean signature set (the bank)

Four objects are banked **now**, contingent only on the build slice's `#print axioms` = trio. Nothing
else is banked. `open NumberField` is mandatory (`𝓞` is not exported by `GaloisRep.lean`'s
module-scoped open — confirmed Stage 4 §, Stage 5 §4.1).

```lean
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient

open NumberField

namespace FLT.PotentialModularity.ClassField

/-- Bank #1 — finite-order rank-one carrier predicate.
    `[Nontrivial A]` is load-bearing (kills the `ZMod 1` degenerate character, CE-1).
    Reuses the continuity-carrying `GaloisRep`; never a bare `MonoidHom` (CE-3). -/
def IsFiniteOrderCharacter
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A) : Prop :=
  (Set.range (fun σ => χ σ)).Finite

/-- Bank #2 — prescribed-local-components RELATION (not globalization, not reciprocity).
    Reuses the existing `GaloisRep.toLocal` (`GaloisRep.lean:309`); pure equality of local restrictions. -/
def HasPrescribedLocalComponents
    {F : Type*} [Field F] [NumberField F]
    {A : Type*} [CommRing A] [Nontrivial A] [TopologicalSpace A]
    (χ : GaloisRep F A A)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (χloc : ∀ v ∈ S, GaloisRep (v.adicCompletion F) A A) : Prop :=
  ∀ v (hv : v ∈ S), χ.toLocal v = χloc v hv

variable (K : Type*) [Field K] [NumberField K]

/-- Bank #3 — multiplicative principal ideles.
    The in-Mathlib `AdeleRing.principalSubgroup` is `AddSubgroup` (additive-only,
    `AdeleRing.lean:70`), so the multiplicative version must be defined here. -/
noncomputable def principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range

/-- Bank #4 — idele-class group as a topological commutative group.
    Uses Mathlib's `Units` embedding topology (into `M × Mᵐᵒᵖ`), i.e. the CORRECT idele topology;
    the `IsOpenUnits.lean:22` warning rules out only the naive 𝔸-subspace topology (CE-5). -/
noncomputable def IdeleClassGroup := (AdeleRing (𝓞 K) K)ˣ ⧸ principalIdeles K

end FLT.PotentialModularity.ClassField
```

**Not banked, by explicit decision (requirement 3):** π₀ group structure (type elaborates; instances
blocked — Stage 5 §4.3 diamond), `Kˣ`-discreteness/closedness, Hausdorff/local-compactness,
profiniteness of π₀, any Artin/reciprocity map, any globalization existence, the tame-residue kernel
theorem. Each has a named owner in §2. No `inducedRepresentation` / `Representation.ind` (forgets
continuity + finite-index → FLT-INDUCED-MOD).

---

## 2. Minimal dependency DAG + source/owner table

### 2a. Component DAG (corrected; edges deliberately absent are stated)

```
BANK NOW (axiom-trio, no math claim):
  P1  CF-CHAR      IsFiniteOrderCharacter, HasPrescribedLocalComponents   [defs; 2× Lean-verified]
  P2  CF-IDELE-OBJ principalIdeles, IdeleClassGroup                       [defs; 1× Lean-verified]

BLOCKED — plumbing, not mathematics:
  P3  π₀ group structure on IdeleClassGroup   (Normal/IsMulCommutative/Mul-diamond, Stage 5 §4.3)

DEFINITION-GAP — elementary, NO CFT edge, on the live MLT critical path:
  T1  T-TAME-RESIDUE   tameResidueChar : localInertiaGroup v →* κ(v)ˣ  +  kernel theorem
        └─ discharges TODO @ AbsoluteGaloisGroup.lean:176
        └─ semantic backing for the live consumers (ledger §2c)

MISSING MATHEMATICS — gated, off the immediate critical path:
  T2a T-DISCRETE       principalIdeles closed/discrete in ideles     (needs archimedean bridges)
  T2b T-GLOBAL-RECIP   π₀(IdeleClassGroup) ≃ₜ* Γᵃᵇ  + ϖ↦arith-Frob-mod-inertia coset + local compat
        gated on {P3, T2a, CFT source-register row, T2 review}
        └─► future consumers FLT-INDUCED-MOD, FLT-AUX-CURVE (proof-graph.ndjson:88,91)
  T3  T-CHAR-GLOBALIZE  Grunwald–Wang existence — ODD-ORDER sub-case first (CE-2)   gated on T2b

HOLD — off critical path, no live consumer:
  T-LOCAL-RECIP   Kᵥˣ ≃ₜ* (W_{Kᵥ})ᵃᵇ   (local Weil group absent; chtopbestiary.tex \notready)

ROUTED OUT (requirement 4):
  Skinner_Wiles_CFT_trick   → FLT-AUX-LOCAL-FIELD   (\uses of modularity_lifting, ch04overview.tex:68)
  det/cond(Ind χ) bookkeeping → FLT-INDUCED-MOD

EDGES DELIBERATELY ABSENT:
  T-LOCAL-RECIP → T1   (reciprocity is NOT upstream of the elementary tame-residue map — Stage 1 had
                        this backwards; the repo already committed to the elementary Kummer route)
  any CF-* → IsAutomorphicOfLevel / auxiliary-curve / automorphy   (circularity guard)
```

### 2b. Source / owner table

| Interface | State today | Source locator | Owner / gate |
|---|---|---|---|
| `IsFiniteOrderCharacter`, `HasPrescribedLocalComponents` | exact, 2× Lean-verified | n/a — kernel-clean **definitions**, not T2 assumptions | **bankable now** (P1) |
| `principalIdeles`, `IdeleClassGroup` | exact, 1× Lean-verified (Stage 5) | n/a — definitions | **bankable now** (P2), pending build-slice re-confirm |
| π₀ group object | type OK; instances fail | n/a — definition | **P3 plumbing** (dedicated file registering `Normal`/`CommGroup`/`IsMulCommutative`) |
| `tameResidueChar` + kernel theorem | constructible, not written; owns TODO@`AbsoluteGaloisGroup.lean:176` | Serre, *Local Fields* (GTM 67) Ch. IV §2 — **exact prop. # NOT yet fixed** | **T1**, NOT T2-nameable yet (locator gate open) |
| `T-DISCRETE` | missing math | Cassels–Fröhlich (product formula) — unregistered | **T2a** |
| `T-GLOBAL-RECIP` | not stateable (P3+T2a open); clause vocab exists | Cassels–Fröhlich Ch. VII (Tate) — **§ not fixed** | **T2b**, both gates open |
| `T-LOCAL-RECIP` | not stateable (Weil group absent) | Cassels–Fröhlich Ch. VI (Serre) — unregistered | **HOLD** |
| `T-CHAR-GLOBALIZE` | not honestly stateable | Artin–Tate Ch. X — unregistered | **T3**, odd-order first |

**Source-register truth (verified):** `SRC-004` = FLT blueprint, "Read; explicitly incomplete
upstream" (`SOURCE-REGISTER.md:12`). The register (SRC-001…) contains **no CFT primary source**. The
T2 policy `HIST-UNRESOLVED` (`historical-assumptions.ndjson:1`) forbids any T2 assumption "until an
exact Lean type **and** primary-source locator have been independently reviewed." **Therefore no CFT
locator is fabricated and no T2 is authorized here** (requirement 5). The book/chapter hints above are
candidates for a future register row, not authorizations.

### 2c. Consumer ledger (corrected — the graph is stale)

Live compiled consumers (verified this session), which the proof-graph does **not** record:

| Consumer | Locator | Uses |
|---|---|---|
| `BlueprintSGood.traceOnJ` | `FLT/ModularityLifting/Conditions.lean:40` | `∀ σ ∈ localTameAbelianInertiaGroup v, trace = 2` |
| `traceConditionFunctor` | `FLT/Deformations/LiftFunctor.lean:129` | `∀ σ ∈ localTameAbelianInertiaGroup v, trace = 2` |
| `narrowTraceConditionFunctor` | `FLT/Deformations/LiftFunctor.lean:138` | `∀ σ ∈ localInertiaGroup v, trace = 2` (full inertia, not tame-abelian) |
| `cyclic_base_change` (`hρtame`) | `FLT/GaloisRepresentation/Automorphic.lean:186` | `localTameAbelianInertiaGroup w ≤ δ.ker`, `δ : GaloisRep Kᵥ A A` rank-one |

**Graph reality:** node `FLT-CLASS-FIELD` (`proof-graph.ndjson:17`) has `direct_dependencies: []`,
`lean_declaration: classField_package`, `library_candidates:
["NumberField.AdeleRing","IsLocalClassField","ContinuousCharacter"]`, and only two out-edges:
`E-CLASS-FIELD-INDUCED-MOD` (:88), `E-CLASS-FIELD-AUX-CURVE` (:91). So: (a) the live MLT consumer
relationship is **unrecorded**; (b) `library_candidates` is **1/3 real** — `NumberField.AdeleRing`
exists; `IsLocalClassField` and `ContinuousCharacter` do **not** exist at this SHA. **Ledger
correction is REQUIRED but NOT executed here** (read-only): add a class-field → MLT consumer edge, fix
`library_candidates`, and (later, under review) add a CFT source row.

---

## 3. Normalization freeze (requirement 2)

`GaloisRep.IsAutomorphicOfLevel` (`Automorphic.lean:70–101`) is the binding authority. Verified body:
with `Frob := Field.AbsoluteGaloisGroup.adicArithFrob` (**arithmetic** Frobenius,
`AbsoluteGaloisGroup.lean:213`) it requires, at every good `v`:
`(ρ.toLocal v (Frob v)).det = v.1.absNorm` and `trace (ρ.toLocal v (Frob v)) = π(T_v)`.

**Frozen convention:** any future local/global Artin map sends a local **uniformizer** to the **coset
of an ARITHMETIC Frobenius**, mod the image of `localInertiaGroup v`.
- **Not geometric** — Stage 3's "arithmetic Artin map, uniformizer ↦ geometric Frobenius" is
  internally inconsistent (Stage 4 flagged; CE-3 below is the sign-error proof).
- **Not an element-level uniformizer equality** — the Frobenius class in `Γᵃᵇ` is well-defined only
  mod inertia image, so `T-GLOBAL-RECIP` must state a **coset condition**, never
  `rec(ϖ) = adicArithFrob v` as elements (CE-4). This is exactly the conflation requirement 2 forbids.

The vocabulary to phrase this already exists (all verified): `localUniformiserUnit`
(`LocalUnits.lean:91`), `adicArithFrob` (`AbsoluteGaloisGroup.lean:213`),
`absoluteGaloisGroup.map (algebraMap K Kᵥ)`, `Field.absoluteGaloisGroupAbelianization` (Mathlib).

---

## 4. First no-axiom probe / build slice

Single new probe file (mirrors `FLTMethodology/Probes/MLTSourceBoundary.lean` conventions; the
`Probes/` dir has no ClassField probe yet). **Authoring/registering it is the implementer's first
step — not done in this read-only pass.**

- **File:** `FLTMethodology/Probes/ClassFieldCharacterBoundary.lean` — body = the exact §1 block
  followed by:
  ```lean
  #print axioms FLT.PotentialModularity.ClassField.IsFiniteOrderCharacter
  #print axioms FLT.PotentialModularity.ClassField.HasPrescribedLocalComponents
  #print axioms FLT.PotentialModularity.ClassField.principalIdeles
  #print axioms FLT.PotentialModularity.ClassField.IdeleClassGroup
  ```
- **Register** the module in `FLTMethodology.lean`.
- **Build gate:** `lake build FLTMethodology.Probes.ClassFieldCharacterBoundary`
- **Pass = every `#print axioms` is exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.**
  Only on a green gate are Bank #1–#4 promoted. π₀ is **excluded** (P3); no theorem about any object
  is asserted by the probe. Interface elaboration is not mathematical proof.

---

## 5. Residual gaps (explicit owners)

1. **T1 tame-residue kernel theorem** — construct `tameResidueChar` and prove
   `localTameAbelianInertiaGroup v = ker`, discharging `AbsoluteGaloisGroup.lean:176`. Elementary
   (Kummer/Serre Ch. IV §2); **no CFT edge**. Stateable-now warm-up (no new defs):
   `localTameAbelianInertiaGroup v ≤ localInertiaGroup v`. Register needs the exact Serre prop. #.
2. **P3 π₀ group structure** — typeclass plumbing (Normal/CommGroup/IsMulCommutative, Mul-diamond).
3. **T2a discreteness/closedness of `principalIdeles`** — missing math (archimedean + product formula).
   Precondition for any π₀ *theorem* (non-Hausdorff quotient makes π₀ semantically fragile, CE-8).
4. **T2b global reciprocity** + local–global compat clause — gated on {P3, T2a, source row, T2 review}.
5. **T3 Grunwald–Wang** — odd-order sub-case only (unconditionally non-exceptional); full statement
   needs an explicit non-exceptionality predicate that does not yet exist.
6. **HOLD T-LOCAL-RECIP** — local Weil group absent; off critical path.
7. **Ledger edits** (§2c) — required, not executed.

## 6. Counterexamples / stop-loss gates

- **CE-1** `A = ZMod 1` (subsingleton) accepts a degenerate character ⇒ `[Nontrivial A]` mandatory.
- **CE-2** Grunwald–Wang: no cyclic deg-8/ℚ with local degree 8 at 2 ⇒ unconditional prescribed-local
  existence is **false**; odd-order first, exceptional set explicit only when 2-primary theory is built.
- **CE-3** geometric normalization forces `det ρ(Frobᵥ) = N(v)⁻¹`, contradicting `IsAutomorphicOfLevel`'s
  `= N(v)` at every good place — a first-lemma sign error. Arithmetic normalization is pinned by code.
- **CE-4** `rec(class of localUniformiserUnit v) = adicArithFrob v` as an **element** equality in `Γᵃᵇ`
  is ill-posed — well-defined only mod `localInertiaGroup v` image ⇒ coset statement only.
- **CE-5** 𝔸-subspace topology makes inversion discontinuous (`IsOpenUnits.lean:22`) ⇒ use Mathlib's
  `Units` embedding topology (Bank #4 does), introduce no bespoke topology.
- **CE-6** (kills the finite-idele shortcut) for `K = ℚ`, `coker(FiniteAdeleRing.unitEmbedding) ≅
  Ẑˣ/{±1}` whereas `π₀(𝔸_ℚˣ/ℚˣ) ≅ Ẑˣ` — the finite cokernel drops complex conjugation (character
  parity) that FLT-INDUCED-MOD needs. **Stage 3's "cokernel of `unitEmbedding` = idele class group" is
  wrong**, not merely incomplete.
- **CE-7** no live consumer distinguishes the tame character `t_v` from `t_v⁻¹` (all use it via
  membership/`≤ ker`, inversion-stable) ⇒ direction is a **recorded convention**, not a compile-gating
  theorem, until `T-LOCAL-RECIP` compat exists.
- **CE-8** π₀ over a non-Hausdorff quotient is premature ⇒ T2a precedes any π₀ theorem (objects unaffected).

**Stop-losses:** **S1** if idele-discreteness/restricted-product bridges don't land, T2b stays a named
gap — keep P1/P2/T1. **S2** any reappearance of Skinner–Wiles or induction bookkeeping inside a CF
node ⇒ REVISE. **S3** discharged by scope-restriction (odd-order). **S4** solvable-field work stays in
FLT-AUX-LOCAL-FIELD. **Circularity guard holds:** no CF-* node references `IsAutomorphicOfLevel`,
automorphy, or curve existence (checked against every §1 signature).

---

## 7. Verdict

**`READY-FOR-GPT-REVIEW`.** The omnibus `classField_package` is replaced by: four axiom-clean banked
objects (2 predicates 2×-verified, 2 idele objects 1×-verified, all gated on the §4 probe); an
elementary tame-residue node (T1) that backs the **live compiled MLT consumers** and is kept off the
local-reciprocity path per requirement 1; the arithmetic-Frobenius normalization frozen from
`IsAutomorphicOfLevel` as a coset (not element) convention per requirement 2; discreteness,
profiniteness, Artin reciprocity, globalization, and π₀ group structure held as named gaps with exact
owners per requirement 3; odd-order Grunwald–Wang preserved and Skinner–Wiles / induced bookkeeping /
automorphy / curve existence routed out per requirement 4; and the DAG + consumer ledger corrected
**without** fabricating a CFT locator or authorizing T2 per requirement 5. No repository file, control
record, axiom, or obligation was edited or promoted; no production Lean was built.

### Verification checklist (all confirmed first-hand this session)
- `localTameAbelianInertiaGroup` def + TODO — `AbsoluteGaloisGroup.lean:176,178` ✓
- 3 tame-abelian consumers + 1 full-inertia consumer — `Conditions.lean:40`, `LiftFunctor.lean:129,138`,
  `Automorphic.lean:186` ✓
- Arithmetic-Frobenius normalization `det = absNorm` — `Automorphic.lean:70–101`, `adicArithFrob:213` ✓
- `GaloisRep.toLocal` abbrev — `GaloisRep.lean:309` ✓
- `AdeleRing.principalSubgroup` is `AddSubgroup` (additive-only) — `AdeleRing.lean:70` ✓
- proof-graph edges + stale `library_candidates` — `proof-graph.ndjson:17,88,91` ✓
- SRC-004 incomplete, no CFT source — `SOURCE-REGISTER.md:12` ✓
- T2 policy — `historical-assumptions.ndjson:1` ✓
- `localUniformiserUnit` — `LocalUnits.lean:91` ✓

