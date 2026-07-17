# Opus 4.8 primary design output

Component: `brauer-nesbitt / FLT-BRAUER-NESBITT`
Agent: `opus48-primary-designer-d8`
Model/backend: `claude-opus-4-8` / `claude-code`
Verdict: **READY-FOR-GPT-REVIEW**
Bridge duration: 922181 ms
Claude session: `d88cbc33-ff7b-4fb8-9ebb-3c62bb4c5d15`

The model completed within its scheduled difficulty budget. Claude's plan-mode transport wrote the
full report to `/Users/philiphaynes/.claude/plans/primary-opus-4-8-design-jazzy-sonnet.md` despite the read-only prompt and returned only a summary to the bridge.
That out-of-repository provider side effect is recorded honestly; the report below is the complete
plan artifact copied into the governed component directory. No external file was edited or deleted
by this orchestration step.

---

# PRIMARY OPUS 4.8 DESIGN — BRAUER–NESBITT (Stage-1, read-only)

**Role:** first-attempt primary producer under the Opus-first ladder. Output feeds GPT adversarial review.
**Mode:** read-only design. No repository edits. Kernel evidence, not source familiarity, is the eventual completion authority.
**Repository:** `/Volumes/second-store/devel/proof-forks/FLT`. Frozen baseline SHA `827eb96…` (branch `methodology/varro-proof-program-20260716`).

---

## Context

`FLT-BRAUER-NESBITT` is a critical-path graph root. Its statement (`FLT.Components.BrauerNesbitt.Contract`)
is frozen and kernel-clean; the terminal proof is **absent**. Three downstream obligations consume it
(`FLT-MLT-COEFFICIENTS`, `FLT-CHEBOTAREV`, `FLT-COMPAT-CONTRA`). Prior boundary reviews (Fable5,
GPT-5.6xhigh) returned **REVISE**, unanimously recommending the arbitrary-field umbrella be *retained*, and
flagged the documented separable splitting-field route as **incomplete over imperfect fields**. This design
selects the smallest true theorem surface serving all live consumers, resolves the arbitrary-field vs
split-branch question, and specifies exact Lean signatures + a bounded, buildable first slice.

---

## VERDICT: `READY-FOR-GPT-REVIEW`

**Architecture = retain the unchanged arbitrary-field umbrella `Contract`.** Both live Lean consumers are
served by it; the char-0 Chebotarev consumer does not yet exist in code and is a *separate* branch, not part
of this contract. The proof is reduced, in dependency order, to (i) an **already-de-risked** structural slice
(`jointImageAlgebra` is a semisimple ring — buildable now with pinned Mathlib), and (ii) a single load-bearing
**hard core** (arbitrary-field Brauer–Nesbitt multiplicity theorem) that has no Mathlib support and carries the
real risk. The first slice reduces the real terminal (not another equivalent contract) and attaches directly to
the kernel-clean `jointImageAlgebra` definition. Stop-loss tests below fence the hard core.

**Next exact theorem to attempt:** `isSemisimpleRing_jointImageAlgebra` (Section 4, L1).

---

## 1. Observed baseline and consumers

**Contract file** `FLT/Components/Contracts/BrauerNesbitt.lean` (185 lines; no `sorry`/`admit`/`axiom`; audit
`methodology/evidence/contracts/BrauerNesbittContractAudit.lean` pins axiom trio `[propext, Classical.choice, Quot.sound]`):

- `Contract : Prop` (L34) — EXISTING-PROVED *statement*. Arbitrary `[Field k] [Group G]`, `Module.Finite k V/W`,
  both `IsSemisimpleRepresentation`, hypothesis `∀ g, (rho g).charpoly = (sigma g).charpoly` (charpoly on every
  element — **not** trace-only), conclusion `Nonempty (Representation.Equiv rho sigma)`.
- `FiniteJointImageContract : Prop` (L161) — EXISTING-PROVED *statement*. Same, plus a supplied basis
  `g : Fin (Module.finrank k (jointImageSpan rho sigma)) → G` that is `LinearIndependent` and spans `jointImageSpan`.
- `contract_of_finiteJointImageContract` (L176) — **EXISTING-PROVED, kernel-clean**:
  `FiniteJointImageContract.{uK,uG,uV,uW} → Contract.{uK,uG,uV,uW}`. **This is the reduction endpoint the design attaches to.**
- Proved supports: `trace_eq_of_charpoly_eq` (L45), `jointImagePoint` (L78), `jointImageSpan` (L82),
  `jointImageAlgebra` (L86, `noncomputable`, subalgebra of `Module.End k V × Module.End k W`), `jointImageFst/Snd`
  (L112/118, `A →ₐ[k] Module.End k V` / `… W`), `jointImageElement` (L124), `exists_jointImage_basis_from_group` (L141).

**Actual Lean consumers** (genuine term dependencies) — both in `FLTMethodology/Probes/BrauerNesbittBoundary.lean`,
and both consume a **local statement-twin `GroupContract` (L27)**, *not yet the component `Contract`*. Nothing in-repo
currently consumes the component `Contract`/`FiniteJointImageContract` as a term (only `FLT.lean:16` import wiring and
the `#check`/`#print axioms` audit reference it).

| Consumer | File:line | Coefficient regime | Equality hypothesis actually needed | Served by umbrella? |
|---|---|---|---|---|
| `semisimplifiedResidualModelsUnique_of_groupContract` | L348 | **arbitrary field** `k` | full charpoly on every `g` (via `GroupContract`) | **Yes — directly** |
| `specializedResidualModelsUnique` | L405 | alg-closed, `finrank=2`, `2 < ringChar k` (odd) | trace-only (via `AlgClosedTwoDimensionalTraceContract`) | **Yes — its conclusion is a special case of Consumer 1's** |

Both produce the same target `SemisimplifiedResidualModelsUnique` (`FLTMethodology/Probes/MLTSourceBoundary.lean:89`).
Consumer 1 proves it for *arbitrary* `k`, so it subsumes Consumer 2's alg-closed rank-2 conclusion; Consumer 2 exists
only as a narrower fallback requiring a weaker (trace-only) input contract.

**Graph-only / absent consumers.** `FLT-MLT-COEFFICIENTS` (definition-gap, ℓ-adic residual), `FLT-CHEBOTAREV`
(absent, char-0 compatible family, "almost-all Frobenius"), `FLT-COMPAT-CONTRA` (absent). The **char-0
compatible-family / Chebotarev consumer does not exist as a Lean declaration** — it is future work gated behind
`FLT-CHEBOTAREV`, and its hypothesis (almost-all Frobenius equality) is *not* the all-group-elements hypothesis of
this contract. `SmallDimensionTraceContract` (L263, char-0-admitting) and `SimpleCharactersLinearIndependentContract`
(L251, alg-closed) are unconsumed frozen statements.

---

## 2. Source theorem boundary

- **SRC-018** = Brauer–Nesbitt, *On the Regular Representations of Algebras*, PNAS 23 (1937) — **PRIMARY**, visually
  checked, but scoped to *algebraically closed field / regular representations*. It does **not** state the modern
  arbitrary-field group contract. Do not upgrade it.
- **SRC-019** = Wiese, *Galois Representations*, Thm 2.4.6 + Remark 2.4.7(iii) — **SECONDARY**; gives the exact modern
  statement and a proof route, but the route (separable splitting field + Frobenius/Galois descent) is **incomplete
  over imperfect fields** (a finite purely inseparable extension need not admit the finite separable splitting field
  the route uses). Do not upgrade Wiese's notes beyond a secondary source.

**Decision.** The unchanged arbitrary-field theorem is **TRUE** and has an adequate *secondary* source (Wiese) plus a
standard arbitrary-field treatment in the algebra literature (Curtis–Reiner, *Methods of Representation Theory I*,
§30 — Brauer–Nesbitt over arbitrary fields; **register as a candidate primary/independent source to close the source
gate — flagged, not asserted as verified here**). The umbrella is the right contract; two consumer-specialized
terminals are **not** safer, because (a) both live consumers are already served by the umbrella and (b) removing the
umbrella is forbidden by both prior reviews and both consumer-narrowing reviews ("NARROWING PARTIAL ONLY").
Source-gate residue: an *exact primary* locator for the arbitrary-field group statement is still open; this is a
programme source obligation, not a mathematical obstruction.

---

## 3. Architecture choice — (a) imperfect-field-safe umbrella

**Choose (a): prove the unchanged umbrella `Contract`, via the existing `FiniteJointImageContract` reduction, along
an imperfect-field-safe path that avoids splitting fields entirely.** Route:

```
Contract                                   -- EXISTING-PROVED statement
  ⇧ contract_of_finiteJointImageContract   -- EXISTING-PROVED (kernel-clean)
FiniteJointImageContract                   -- EXISTING-PROVED statement; TARGET to prove
  ⇧ [PROPOSED L4 assembly]
A-module isomorphism  V ≃ₗ[A] W            -- A := jointImageAlgebra rho sigma
  ⇧ [PROPOSED L3: hard core — arbitrary-field Brauer–Nesbitt multiplicity theorem]
A is a f.d. semisimple k-algebra; V, W f.d. semisimple faithful A-modules
  ⇧ [PROPOSED L1 (first slice) + L2 module structure/semisimplicity]  -- BUILDABLE NOW
jointImageAlgebra, jointImageFst/Snd, isSemisimpleRepresentation_iff_isSemisimpleModule_asModule  -- EXISTING-PROVED
```

**Why complete.** (1) The joint image `A = jointImageAlgebra rho sigma` is a *finite-dimensional* subalgebra of
`Module.End k V × Module.End k W`, so it is Artinian and needs no splitting field. (2) `V`, `W` are semisimple
*faithful* `A`-modules, so `A` is a semisimple ring (`Ring.jacobson A ≤ ann_A(V×W) = ⊥`, Artinian ⇒ semisimple).
(3) The terminal reduces to: two f.d. modules over a f.d. *semisimple* `k`-algebra with equal characteristic
polynomials on the group-image generators are isomorphic — the pure-algebra Brauer–Nesbitt, provable *directly over
the base field* with no separable descent. (4) An `A`-linear iso is automatically `k[G]`-equivariant (the `k[G]`
action factors through `A`), producing `Representation.Equiv`. No public conclusion is weakened; the residual and
char-0 consumers are both served (char-0 Chebotarev separately, once it exists, reusing the same umbrella).

**Split-branch alternative — tested and rejected as the terminal.** Keep as *fallback only*: if L3 proves
intractable, the already-proved `specializedResidualModelsUnique` (alg-closed rank-2 odd-char) discharges the
residual consumer, and a distinct char-0 branch discharges Chebotarev. This is strictly weaker (narrowing), leaves
the graph root open, and is disallowed as a *replacement* by both reviews. Adopt only under the Section 8 stop-loss.

---

## 4. Exact Lean signatures in dependency order

Namespace `FLT.Components.BrauerNesbitt`, `open Representation`, universes `uK uG uV uW`, with
`variable {k G V W} [Field k] [Group G] [AddCommGroup V] [Module k V] [Module.Finite k V]`
`[AddCommGroup W] [Module k W] [Module.Finite k W] (rho : Representation k G V) (sigma : Representation k G W)`.
Dependency labels: **EXISTING-PROVED**, **EXISTING-ADMITTED** (none used), **PROPOSED**.

### L0 — module structures (PROPOSED, defs; attach to EXISTING-PROVED `jointImageFst/Snd`)
```lean
/-- `V` as a module over the joint-image algebra, by restriction along the first projection. -/
noncomputable def fstModule : Module (jointImageAlgebra rho sigma) V :=
  Module.compHom V (jointImageFst rho sigma).toRingHom

/-- `W` as a module over the joint-image algebra, by restriction along the second projection. -/
noncomputable def sndModule : Module (jointImageAlgebra rho sigma) W :=
  Module.compHom W (jointImageSnd rho sigma).toRingHom
```
Provide `IsScalarTower k (jointImageAlgebra rho sigma) V` (and `W`), and the `simp` fact
`(jointImageElement rho sigma g) • (x : V) = rho g x` (via `jointImageFst_element`, EXISTING-PROVED L129).

### L1 — FIRST BUILDABLE SLICE (PROPOSED; attaches to EXISTING-PROVED `jointImageAlgebra`)
```lean
/-- The joint-image algebra is a finite-dimensional semisimple k-algebra. -/
theorem isSemisimpleRing_jointImageAlgebra
    (hrho : Representation.IsSemisimpleRepresentation rho)
    (hsigma : Representation.IsSemisimpleRepresentation sigma) :
    IsSemisimpleRing (jointImageAlgebra rho sigma)
```
Proof sketch (all cited decls PRESENT): `Module.Finite k (jointImageAlgebra rho sigma)` from `Submodule.finite`
of `Module.End k V × Module.End k W` ⇒ `IsArtinianRing`. `letI := fstModule …; letI := sndModule …`; `V × W` is a
faithful `A`-module (the `A ↪ Module.End k V × Module.End k W` inclusion recovers both coordinate actions, so
`Module.annihilator A (V × W) = ⊥`). `V`, `W` are semisimple `A`-modules (L2 below) ⇒ `V × W` semisimple ⇒
`IsSemisimpleModule.jacobson_le_annihilator : Ring.jacobson A ≤ Module.annihilator A (V×W) = ⊥`, then
`IsArtinian.isSemisimpleModule_iff_jacobson A A` gives `IsSemisimpleRing A`.

### L2 — module semisimplicity transport (PROPOSED)
```lean
theorem isSemisimpleModule_fst
    (hrho : Representation.IsSemisimpleRepresentation rho) :
    letI := fstModule rho sigma
    IsSemisimpleModule (jointImageAlgebra rho sigma) V
-- and symmetrically `isSemisimpleModule_snd … (hsigma) … W`.
```
Proof: `rho` semisimple ⇔ `IsSemisimpleModule k[G] rho.asModule`
(`isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`, EXISTING-PROVED). The `A`-action on `V` factors the
`k[G]`-action through the surjection `k[G] ↠ A` (range of `(rho.prod sigma).asAlgebraHom` corestricted to `A`);
restriction of scalars along a surjective ring hom preserves semisimplicity (submodule lattices coincide).

### L3 — HARD CORE (PROPOSED; NO Mathlib support — load-bearing risk)
```lean
/-- Arbitrary-field Brauer–Nesbitt multiplicity theorem: over a finite-dimensional semisimple k-algebra,
    two finite-dimensional modules whose group-generated characteristic-polynomial data agree are isomorphic. -/
theorem linearEquiv_of_charpoly_eq_group
    {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module.Finite k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module.Finite k N] [Module A N] [IsScalarTower k A N]
    (U : Set Aˣ) (hspan : Submodule.span k ((↑) '' (U : Set Aˣ) : Set A) = ⊤)
    (hchar : ∀ u ∈ U,
      (LinearMap.charpoly (Algebra.lsmul k k M (u : A))) =
      (LinearMap.charpoly (Algebra.lsmul k k N (u : A)))) :
    Nonempty (M ≃ₗ[A] N)
```
**Statement risk — must be verified TRUE before freezing (Section 6):** charpoly is nonlinear, so equality on a
*spanning set of units* is not free. The intended proof upgrades to the multiplicity comparison via the
Artin–Wedderburn decomposition `A ≃ₐ ∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) (Dᵢ)`
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`, PRESENT), the isotypic decompositions
`M ≃ₗ[A] Fin mᵢ → Sᵢ` (`IsIsotypic.linearEquiv_fun`, PRESENT), and charpoly multiplicativity
`charpoly(a, M) = ∏ᵢ charpoly(a, Sᵢ)^{mᵢ}`; the *unit* hypothesis and the group closure are what let the
constituent multiplicities be separated over an arbitrary (incl. imperfect) base field without a splitting field.
This lemma is where the imperfect-field difficulty concentrates and where no Mathlib lemma exists.

### L4 — assembly to the frozen reduction (PROPOSED; discharges EXISTING-PROVED statement `FiniteJointImageContract`)
```lean
theorem finiteJointImageContract : FiniteJointImageContract.{uK, uG, uV, uW}
```
Proof: intro data; `letI` the L0 module structures; `A := jointImageAlgebra rho sigma`; L1 gives
`IsSemisimpleRing A`; take `U := Set.range (fun g => Units-lift of jointImageElement rho sigma g)` (group elements
are units of `A`), `hspan` from the supplied basis hypothesis (the group-image basis spans `jointImageSpan = A`),
`hchar` from `∀ g, (rho g).charpoly = (sigma g).charpoly` rewritten through `jointImageFst_element`/`jointImageSnd_element`;
apply L3 to get `e : V ≃ₗ[A] W`; build `Representation.Equiv rho sigma` via `Representation.Equiv.mk` with the
underlying `k`-linear equiv (from `IsScalarTower`) and intertwining `∀ g, e ∘ₗ rho g = sigma g ∘ₗ e` (immediate: both
sides are the `A`-action of `jointImageElement rho sigma g` and `e` is `A`-linear).

Then `theorem brauer_nesbitt : Contract := contract_of_finiteJointImageContract finiteJointImageContract`
(matches graph `lean_declaration` `FLT.Representation.brauer_nesbitt`, module `FLT.RepresentationTheory.BrauerNesbitt`).

---

## 5. Pinned-library matches (Mathlib rev `a3364faec42918fcd84a03a255b50570129f9ead`)

| Need | Mathlib declaration | File | Class |
|---|---|---|---|
| semisimple ⇔ jacobson ⊥ (Artinian) | `IsArtinian.isSemisimpleModule_iff_jacobson` | `RingTheory/Artinian/Module.lean:281` | **exact** |
| rad ≤ annihilator of s.s. module | `IsSemisimpleModule.jacobson_le_annihilator` | `RingTheory/Jacobson/Semiprimary.lean:44` | **exact** |
| annihilator ⊥ ⇔ faithful | `Module.annihilator_eq_bot` | `RingTheory/Ideal/Maps.lean:886` | **exact** |
| semisimple rep ⇔ s.s. `k[G]`-module | `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule` | `RepresentationTheory/Semisimple.lean:37` | **exact** |
| Artin–Wedderburn explicit decomposition | `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing(_finite)` | `RingTheory/SimpleModule/WedderburnArtin.lean:195/204` | **exact** |
| isotypic ⇒ `Fin n → S` | `IsIsotypic.linearEquiv_fun`, `IsIsotypicOfType.linearEquiv_fun` | `RingTheory/SimpleModule/Isotypic.lean:157/151` | **adaptable** |
| isotypic components cover / independent / finite | `sSup_isotypicComponents`, `sSupIndep_isotypicComponents`, `Finite (isotypicComponents …)` | `RingTheory/SimpleModule/Isotypic.lean:478/288/302` | **adaptable** |
| charpoly of a linear map | `LinearMap.charpoly`, `charpoly_toMatrix` | `LinearAlgebra/Charpoly/Basic.lean:44` | **exact** |
| charpoly similarity-invariance | `Matrix.charpoly_units_conj(')` | `LinearAlgebra/Matrix/Charpoly/Basic.lean:280/286` | **exact** |
| charpoly base change | `LinearMap.charpoly_baseChange` | `LinearAlgebra/Charpoly/BaseChange.lean:23` | **adaptable** (not needed if no splitting field) |
| `Representation.Equiv` builder | `Representation.Equiv.mk` | `RepresentationTheory/Intertwining.lean:~330` | **exact** |
| Maschke (coprime-char s.s.) | `Representation … IsSemisimpleRepresentation` instance | `RepresentationTheory/Maschke.lean:183` | **exact** (not load-bearing; modular case is the point) |

**First genuinely absent algebra theorem:** the **arbitrary-field Brauer–Nesbitt multiplicity comparison** (L3) —
"finite-dimensional modules over a finite-dimensional semisimple `k`-algebra with equal characteristic polynomials
on a group-generating spanning set of units are isomorphic." Mathlib has only `Representation.char_iso` (forward,
trace-only) and `char_orthonormal` (trace-only, requires `[Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]`).
Secondary absent theorem (only if a splitting-field route is ever attempted): **separable base change preserves
`IsSemisimpleRing`/`IsSemisimpleModule`** — absent; this design deliberately avoids needing it.

---

## 6. Counterexamples and statement risks

1. **Imperfect fields.** Splitting-field route fails (inseparable extensions). *Mitigation:* the design never
   passes to a splitting field; it works inside the f.d. joint-image algebra over `k`. L3 must be a base-field proof.
2. **Trace-only positive-characteristic failure.** `refutedOneSidedTraceContract_false`
   (`BrauerNesbittBoundary.lean:311`) exhibits `ZMod 2` trivial reps of dims 1 and 3: equal traces, non-isomorphic.
   *Consequence:* L3 must use full **charpoly**, never trace, and any trace-only weakening must retain rank/dim
   side-conditions (as `AlgClosedTwoDimensionalTraceContract` does).
3. **Charpoly nonlinearity on group algebras.** charpoly is not additive; equality on a *k-basis* of `A` is
   insufficient. *This is the crux of L3.* The hypothesis is charpoly on **all** group elements (units generating
   `A`), which is strictly more than on a basis; the multiplicity extraction must exploit the multiplicative/unit
   structure, not linear extension. **Stop-loss trigger if L3 cannot be stated in a demonstrably true form.**
4. **Finite vs infinite groups.** No group-finiteness hypothesis; `A` finite-dimensional comes from
   `Module.Finite k V/W`, not `Finite G`. Any argument invoking Zariski density of the unit set must handle finite
   base fields separately (the group image can be a finite non-dense unit subgroup).
5. **Semisimplicity transport.** L2 relies on restriction of scalars along the surjection `k[G] ↠ A` preserving
   semisimplicity — true because submodule lattices coincide under a surjective ring map; verify Mathlib has the
   lattice-iso lemma or prove it (small).
6. **Scalar-extension descent.** Not used (design avoids it). If a reviewer insists on the splitting-field route,
   the absent "separable base change preserves semisimplicity" becomes a blocker — a reason to prefer route (a).
7. **Char-0 residual vs rank-two use.** The residual consumer (`FLT-MLT-COEFFICIENTS`) is served by the umbrella;
   the rank-2 alg-closed odd-char shortcut is a fallback. Do not conflate with char-0.
8. **Separate Chebotarev bridge.** `FLT-CHEBOTAREV` (char-0, almost-all Frobenius) is a *distinct* consumer that
   does not exist yet and must not be folded into this contract; its "almost-all Frobenius" hypothesis ≠ the
   all-group-elements hypothesis here.

---

## 7. Smallest buildable first slice

- **Scope:** one theorem, `isSemisimpleRing_jointImageAlgebra` (L1), plus the two module-structure defs (L0) and the
  semisimplicity transport (L2) it depends on. New file (target module) `FLT/RepresentationTheory/BrauerNesbitt.lean`
  or a scratch probe `FLTMethodology/Probes/BrauerNesbittAlgebra.lean`; **do not** edit the frozen contract file.
- **Bounded proof plan:** (1) `Module.Finite k A` ⇒ `IsArtinianRing A`; (2) L0 module structures + `IsScalarTower`;
  (3) L2 semisimplicity of `V`, `W`, hence `V × W`, as `A`-modules; (4) faithfulness ⇒ `Module.annihilator A (V×W) = ⊥`;
  (5) `jacobson_le_annihilator` + `isSemisimpleModule_iff_jacobson` ⇒ `IsSemisimpleRing A`.
- **Targeted build/audit commands:**
  `lake build FLTMethodology.Probes.BrauerNesbittAlgebra` (or the target module);
  then `#print axioms isSemisimpleRing_jointImageAlgebra` — must be `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- **First likely residual Lean goal:** after `rw [← IsArtinian.isSemisimpleModule_iff_jacobson]` and discharging the
  annihilator, the open goal is `Module.jacobson (jointImageAlgebra rho sigma) (jointImageAlgebra rho sigma) = ⊥`,
  reduced to `Ring.jacobson A ≤ Module.annihilator A (V × W)` with the faithfulness `Module.annihilator A (V × W) = ⊥`;
  the fiddly sub-goal is exhibiting the faithful `A`-action instance on `V × W` compatibly with L0.
- **It reduces the real terminal:** L1 converts the group-representation problem to a pure semisimple-algebra
  problem — a genuine structural step used by L3/L4 — not another equivalent contract.

---

## 8. Dependency graph and gates

**Local DAG:** `EXISTING-PROVED{jointImageAlgebra, jointImageFst/Snd, jointImageElement, isSemisimpleRepresentation_iff…}`
→ `L0` → `L2` → **`L1` (first slice)** → `L3` (hard core) → `L4` → `contract_of_finiteJointImageContract`
(EXISTING-PROVED) → `Contract` / `FLT.Representation.brauer_nesbitt`. Downstream: `FLT-MLT-COEFFICIENTS`,
`FLT-CHEBOTAREV` (separate char-0 branch), `FLT-COMPAT-CONTRA`.

**Completion criterion:** `#print axioms brauer_nesbitt = [propext, Classical.choice, Quot.sound]` with the target
`Contract.{uK,uG,uV,uW}` type, and both live consumers (`semisimplifiedResidualModelsUnique_of_groupContract`,
`specializedResidualModelsUnique`) re-provable from it without any new public assumption.

**Explicit stop-loss tests:**
- **False statement:** if L3 cannot be written in a form provably true over imperfect + finite base fields (charpoly
  nonlinearity / non-dense unit group), STOP the umbrella proof and fall back to the narrowing branch. Regression
  fence: `refutedOneSidedTraceContract_false` must remain provable; any L3 draft implying a trace-only conclusion is
  false by construction.
- **Unavailable descent:** if any sub-proof silently requires "separable base change preserves semisimplicity"
  (absent in Mathlib), reject that sub-proof — route (a) is chosen precisely to avoid it.
- **Source mismatch:** if the arbitrary-field group statement cannot be matched to an exact primary/independently
  reviewed source (SRC-018 insufficient; SRC-019 secondary), the *terminal* stays open under the programme source
  gate even if kernel-clean; register Curtis–Reiner §30 (candidate) for review — do not assert it as verified.

**No proposed assumption** contains `Contract`, `FiniteJointImageContract`, representation equivalence, or consumer
uniqueness as an unproved hypothesis (checked: L0–L4 hypotheses are field/group/module/semisimplicity/charpoly data only).

---

## 9. Verdict

**`READY-FOR-GPT-REVIEW`.** The architecture is settled (retain the arbitrary-field umbrella; split-branch is a
fenced fallback, not a replacement), the reduction DAG is explicit and anchored to the kernel-clean
`contract_of_finiteJointImageContract`, the first slice `isSemisimpleRing_jointImageAlgebra` is concretely buildable
now against pinned Mathlib, and the single load-bearing hard core (L3, arbitrary-field Brauer–Nesbitt multiplicity)
is precisely located with honest risk-flagging and stop-loss. **Next exact theorem/signature to attempt:** L1
`isSemisimpleRing_jointImageAlgebra` (Section 4), then L3 `linearEquiv_of_charpoly_eq_group` — the latter is where GPT
review should concentrate adversarial effort (truth of the statement over imperfect/finite fields; the
charpoly-nonlinearity multiplicity-separation argument).

**Handoff caveat (not a proof):** this is a design, not kernel evidence. L3 has no Mathlib support and no exact
primary source; it must not be treated as proved until it is Lean-checked and its statement adversarially verified.

