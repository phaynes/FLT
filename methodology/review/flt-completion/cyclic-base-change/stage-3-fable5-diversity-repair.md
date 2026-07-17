# Stage-3 Fable 5 Diversity Repair — `cyclic-base-change` / `FLT-CBASE`

**Actor:** Fable 5 diversity-repair designer (hostile mathematical and Lean reviewer), difficulty 10.
**Mode:** read-only; no repository files, control rows, source registrations, task state, or graphs
edited. All Lean evidence obtained by disposable `lake env lean --stdin` probes (no files written).
**Repository:** `/Volumes/second-store/devel/proof-forks/FLT`, toolchain `leanprover/lean4:v4.32.0-rc1`.
**Inputs read:** `stage-1-opus48-primary.md`, `stage-2-gpt56xhigh-review.md`, the admitted
`cyclic_base_change` (`FLT/GaloisRepresentation/Automorphic.lean:137–194`), `IsAutomorphicOfLevel`
(`:70–97`), the pinned representation API (`FLT/Deformations/RepresentationTheory/GaloisRep.lean`,
`…/AbsoluteGaloisGroup.lean`), quaternion API (`FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean`,
`FLT/QuaternionAlgebra/NumberField.lean`), Hecke API
(`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean`), place transport
(`FLT/DedekindDomain/IntegralClosure.lean`, `…/FiniteAdeleRing/BaseChange.lean`), coefficient
instances (`Automorphic.lean:112–117`), blueprint paragraphs (`ch04overview.tex:78–92`,
`chtopbestiary.tex:212–216`, `FLT/Assumptions/README.md:40–65`, `KnownIn1980s.lean`, `blog.md:39`),
`SOURCE-REGISTER.md`, control rows `FLT-CBASE`/`FLT-MLT`/`FLT-MLT-SOURCE`/`FLT-JL`/
`FLT-BRAUER-FAMILY` and edges `E-CBASE-MLT`/`E-CBASE-BRAUER-FAMILY`, and the frozen probe
vocabulary `FLTMethodology/Probes/SelectedGoodRepositoryBoundary.lean`.

## Verdict

# `DESIGN-VIABLE`

Every signature claimed buildable below was probed today and audits to exactly
`[propext, Classical.choice, Quot.sound]`. Every interface claimed statable elaborates against the
built oleans. The two source gates (forward transfer, descent/image) are left **open**: no primary
base-change source is registered in-tree, so this pass names candidate sources without locators and
defers to operator visual verification. This pass authorizes no historical assumption and does not
complete FLT-CBASE.

---

## 0. Hostile verification of the prior artifacts

Confirmed against the kernel, not by reading:

* **Opus D1 fails as written** (GPT defect 1 reproduced). The byte-faithful stage-1 signature
  (`{F E} [Field F] [Field E] [Algebra F E] [FiniteDimensional ℚ F] [FiniteDimensional F E]`) dies
  at elaboration: `failed to synthesize Module ℚ F` (no `CharZero`, so `DivisionRing.toRatAlgebra`
  cannot fire). Probe output retained in §8.
* **GPT's corrected D1 verified**: elaborates and audits to exactly the trio (§2, B1).
* **GPT's D2 probe reproduced independently** (§2, B2a/B2b), including the membership lemma GPT
  used implicitly but did not state.
* **Opus's §2 description of `IsAutomorphicOfLevel` is inaccurate** (new finding, §1-R2): the
  predicate does **not** contain total definiteness. Opus reasoned about a stronger predicate than
  the one in the file.
* **Opus's counterexample 3 ("using `hρirred` in D4 would signal a mis-split") is unsourced and
  mathematically doubtful** (GPT defect 4 corroborated and sharpened, §5).
* **GPT defect 6 confirmed and extended**: the first residual before Hecke transport is not merely
  the missing `DivisionRing`/`WithRigidification` adapters — there is a *type-theoretic* obstruction
  (universes, §1-R1) that precedes even those.

---

## 1. Statement-level findings on the admitted declaration (new in this pass)

**R1 — Universe mismatch blocks every tensor-product provider.**
`cyclic_base_change` binds `{F : Type u₁}` and `{E : Type u₂}` independently (visible in
`#check @cyclic_base_change`). `IsAutomorphicOfLevel {F : Type u}` existentially binds
`D : Type u`; applied to `E` the witness must be `D_E : Type u₂`. The only in-tree base-change
construction is `E ⊗[F] D : Type (max u₁ u₂)` (instance `IsQuaternionAlgebra E (E ⊗[F] D)`,
`Automorphic.lean:99`). `max u₁ u₂ = u₂` is not derivable for unconstrained universes, so no
forward-transfer proof can instantiate the RHS existential via the tensor construction without
ULifting the entire quaternion/Hecke/automorphic-form stack. Repair: all new interfaces below are
stated with a **single universe `u`** for `F`, `E`, `D`. Consumers (FLT-MLT, FLT-BRAUER-FAMILY)
instantiate at concrete number fields in `Type 0`; nothing is lost. Whether the *admitted theorem
itself* should be re-frozen at one universe is an operator decision; until then the two-universe
statement is recorded as unprovable-by-tensor-route.

**R2 — `IsAutomorphicOfLevel` omits total definiteness and even degree.**
The formal existential (`Automorphic.lean:84–88`) requires only
`DivisionRing D`, `Algebra F D`, `IsQuaternionAlgebra F D`,
`IsQuaternionAlgebra.NumberField.WithRigidification F D`. The class
`IsQuaternionAlgebra.IsTotallyDefinite` exists (`FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean:143`)
but enters only at `Concrete.lean:952` (Hecke-module instances) and
`FiniteDimensional.lean` — **not** in `WeightTwoAutomorphicForm`, `HeckeAlgebra`, or the automorphy
predicate. The docstring's "totally definite" is unenforced. Over a field with ≥ 4 real places, a
division algebra split at all finite places need not be totally definite (ramify at a proper even
subset of the infinite places), so the existential ranges over form spaces with no classical
automorphic meaning and no finiteness theorem. This weakens the predicate on both sides of the iff
and is a soundness risk wherever `IsAutomorphicOfLevel` appears as a *hypothesis* (MLT). Ownership:
**FLT-AUT-DEF**, not FLT-CBASE; recorded here as a source-condition risk plus stop-loss gate G3.
No repository edit is proposed by this pass.

**R3 — Frobenius normalization is embedding-dependent.**
`GaloisRep.map` and `adicArithFrob` each make arbitrary choices (`GaloisRep.lean:74–78`,
`AbsoluteGaloisGroup.lean:213`, both documented as arbitrary). Any transport of the trace/det
conditions from `v` to `w | v` is therefore only well-posed up to conjugacy — which is why the
transport interface V8 (§3) is stated on characteristic polynomials, not on endomorphisms.

---

## 2. Smallest presently buildable slice (all probed; exactly the standard trio)

Proposed landing site: **one new methodology probe file**
`FLTMethodology/Probes/CyclicBaseChangeBoundary.lean` (outside the verified `FLT` root, per
`methodology/README.md`: probes are not proof progress; `FLT-CBASE` remains `admitted`). B2a/B2b
and B3 are additionally upstream-PR-able to `FLT/DedekindDomain/IntegralClosure.lean` and
`…/HeckeOperators/Concrete.lean` respectively in a later build-authorized pass.

**B1 — even degree of the top field** (GPT's corrected form, independently re-probed):
```lean
theorem even_finrank_of_even_base
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : Even (Module.finrank ℚ F)) : Even (Module.finrank ℚ E) := by
  rw [← Module.finrank_mul_finrank ℚ F E]
  exact hF.mul_right _
```
Probe: `[propext, Classical.choice, Quot.sound]`. The `NumberField` instances are what make
`Module ℚ _` and the ℚ-tower synthesizable; this is the exact elaborating repair of defect 1.

**B2a — level-pullback membership** (thin place/support transport, the part that is genuinely thin):
```lean
theorem mem_preimageComapFinset_iff
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 E)) :
    w ∈ HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S ↔ w.under (𝓞 F) ∈ S := by
  simp [HeightOneSpectrum.preimageComapFinset, Set.Finite.mem_toFinset]
```
Probe: exactly the trio.

**B2b — good-place transport across the pullback**:
```lean
theorem natCast_notMem_of_mem_preimageComapFinset
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (p : 𝓞 F) ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 E))
    (hw : w ∈ HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S) :
    (p : 𝓞 E) ∉ w.asIdeal := by
  intro hpw
  refine hS (w.under (𝓞 F)) ((mem_preimageComapFinset_iff S w).1 hw) ?_
  have : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w.asIdeal := by
    rw [map_natCast]; exact hpw
  exact Ideal.mem_comap.mpr this
```
Probe: exactly the trio. (This is GPT's proposed next probe, independently re-proved.)

**B3 — Hecke eigensystem rigidity at `Q = ∅` (new; neither prior artifact has it, proved today):**
```lean
theorem heckeAlgebra_algHom_ext
    {F : Type*} [Field F] [NumberField F]
    {D : Type*} [DivisionRing D] [Algebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    {R : Type*} [CommRing R]
    {p : ℕ} (𝒮 : U₁Data F R p) (hQ : 𝒮.Q = ∅)
    {A : Type*} [CommRing A] [Algebra R A]
    (π π' : HeckeAlgebra D 𝒮 →ₐ[R] A)
    (h : ∀ (v : HeightOneSpectrum (𝓞 F)) (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q),
      π (HeckeAlgebra.T D 𝒮 v hvS hvQ) = π' (HeckeAlgebra.T D 𝒮 v hvS hvQ)) :
    π = π' := by
  ext x
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨v, hvS, hvQ, rfl⟩ | ⟨v, hv, α, hα, rfl⟩
      · exact h v hvS hvQ
      · rw [hQ] at hv; exact absurd hv (Finset.notMem_empty v)
  | algebraMap r => exact (π.commutes r).trans (π'.commutes r).symm
  | add x y hx hy ihx ihy =>
      show π (⟨x, hx⟩ + ⟨y, hy⟩) = π' (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      show π (⟨x, hx⟩ * ⟨y, hy⟩) = π' (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
```
Probe: exactly the trio. **Why it matters:** the `cyclic_base_change` level data is
`⟨Fact.out, S, ∅, 1, by simp, hp⟩` — Taylor–Wiles set `Q = ∅` — so the Hecke algebra is generated
by the good operators `T_v` alone, and an eigensystem is *pinned by its good-place values*. This is
**not** multiplicity one and must not be sold as such: multiplicity one is a statement about *forms*
(the eigenspace of a pinned eigensystem is one-dimensional / a form with those eigenvalues exists on
a specific `D`), which is not statable with the pinned API (no automorphic-representation
vocabulary; `library-matches.ndjson:MISS-006`). B3 cleanly demarcates the provable eigensystem half
from the genuinely missing form half — repairing the Opus artifact's conflation of C4 with
descent bookkeeping.

Build gate for this slice: `lake build FLTMethodology.Probes.CyclicBaseChangeBoundary` +
`#print axioms` on all four, expecting exactly the trio (all four already observed today).

---

## 3. Exact interface vocabulary, in dependency order (all elaborated today)

All are `Prop`-valued **definitions** in the `FLTMethodology` namespace — statements, not claims.
None is a production `sorry`; none is an axiom. `#print axioms` on each def reports exactly the
trio (an artifact of noncomputable instance bodies inside the definitions; recorded honestly —
these audits certify *elaboration*, not proof). Single universe `u` throughout (§1-R1). The flat
and tame hypothesis bundles reuse the frozen probe vocabulary
`FLTMethodology.SelectedGoodBoundary.HasFlatDescentAboveEll` / `HasGenericTameRankOneQuotient`
(verbatim `hρflat`/`hρtame`, already standard-trio-clean) instead of restating them — no duplicate
vocabulary.

Dependency order (each item uses only items above it and the pinned API):

**V1 — relational twist** (no smuggled continuity obligation; a *constructed* `GaloisRep.twist`
with its continuity proof is deferred, not needed to state anything downstream):
```lean
def IsTwistBy {K : Type*} [Field K] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (rho' rho : GaloisRep K A M) (chi : GaloisRep K A A) : Prop :=
  ∀ g m, rho' g m = chi g 1 • rho g m
```

**V2 — characters factoring through `Gal(E/F)`** (the invariant-character vocabulary; note
`Field.absoluteGaloisGroup.map` requires `[NumberField F] [NumberField E]` — discovered by probe):
```lean
def FactorsThroughGal (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] (chi : GaloisRep F A M) : Prop :=
  ∀ g : Field.absoluteGaloisGroup E,
    chi (Field.absoluteGaloisGroup.map (algebraMap F E) g) = 1
```

**V5 — Galois-side base-change fiber ("descends up to twist"), statable now, T3-provable in
principle** (finite-index Clifford/Schur theory; *no analytic input*):
```lean
def BaseChangeFiberUpToTwist
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (rho sigma : GaloisRep F A M) : Prop :=
  (∃ e : M ≃ₗ[A] M, (rho.map (algebraMap F E)).conj e = sigma.map (algebraMap F E)) →
    ∃ (e : M ≃ₗ[A] M) (chi : GaloisRep F A A),
      FactorsThroughGal F E chi ∧ IsTwistBy (sigma.conj e) rho chi
```
This is the structural repair of GPT defect 2: the "image characterization with invariant
characters and twists" splits into an **algebraic fiber statement (V5, above — future T3 residual,
no source needed)** and an **analytic surjectivity-onto-invariants statement (form-level, not
statable with the pinned API — definition gap owned jointly with FLT-AUT-DEF/FLT-JL)**. Only the
latter needs a Langlands-type source. Opus's D5 hid both inside one reverse implication.

**V8 — Frobenius/characteristic-polynomial transport at `w | v`** (local compatibility; charpoly
form because of §1-R3; `Ideal.inertiaDeg q R` is the pinned-Mathlib spelling — the naive
`p.inertiaDeg P` fails to elaborate, discovered by probe):
```lean
def FrobeniusCharpolyTransport
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E] [Algebra F E]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    (rho : GaloisRep F A V) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ((rho.map (algebraMap F E)).toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly =
    ((rho.toLocal (w.under (𝓞 F))
        (Field.AbsoluteGaloisGroup.adicArithFrob (w.under (𝓞 F)))) ^
      (w.asIdeal.inertiaDeg (𝓞 F))).charpoly
```

**V6/V7/V9 — the non-thin remainder of "D2", separated as demanded by defect 2.** These are the
conductor/level/local-compatibility content that `preimageComapFinset` does *not* provide; each is
an implication-shaped interface, elaborated today:
```lean
def TameQuotientTransport … : Prop :=
  HasGenericTameRankOneQuotient p rho S →
    HasGenericTameRankOneQuotient p (rho.map (algebraMap F E))
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S)

def UnramifiedTransport … : Prop :=
  (∀ v ∉ S, ↑p ∉ v.asIdeal → rho.IsUnramifiedAt v) →
    ∀ w ∉ HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S,
      ↑p ∉ w.asIdeal → (rho.map (algebraMap F E)).IsUnramifiedAt w

def DetCyclotomicTransport … : Prop :=
  (∀ g, rho.det g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
      (cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv)) →
    ∀ g, (rho.map (algebraMap F E)).det g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
      (cyclotomicCharacter (AlgebraicClosure E) p g.toRingEquiv)
```
(Full binder lists as probed in §8; elided here only for readability — every elision is a binder
block already shown verbatim in V3 below.)
`U₁`-level/conductor matching beyond the tame quotient (new-vector theory) is **form-level** and
remains a definition gap: it cannot be stated against `LocalLevelStruct` without an adelic
`GL₂(𝔸ᶠ[F]) → GL₂(𝔸ᶠ[E])` comparison, for which the available support is
`FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv` (`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:351`)
— present but unconnected to `GL₂`.

**Q1/Q2 — quaternion base-change providers** (defect 4; exact interfaces, elaborated today):
```lean
def BaseChangeUnitsProvider
    (F : Type u) [Field F] [NumberField F] [IsTotallyReal F]
    (E : Type u) [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E]
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D] : Prop :=
  ∀ a : E ⊗[F] D, a ≠ 0 → IsUnit a

def BaseChangeRigidificationProvider
    (F : Type u) [Field F] [NumberField F]
    (E : Type u) [Field E] [NumberField E] [Algebra F E]
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D] : Prop :=
  Nonempty (IsQuaternionAlgebra.NumberField.WithRigidification E (E ⊗[F] D))
```
`BaseChangeUnitsProvider` is stated on `IsUnit` (compatible with the existing ring structure and
with the pinned dichotomy `IsQuaternionAlgebra.nomepty_algEquiv_matrix_or_forall_isUnit`) rather
than `Nonempty (DivisionRing _)`, which would not pin compatibility with the tensor ring structure.

**V3/V4 — the two named boundaries** (defect 3's endpoints; full binder list, probed verbatim):
```lean
def ForwardSolvableBaseChange
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    {E : Type u} [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra F E] [IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]
    (p : ℕ) [Fact p.Prime]
    (hp : 2 < Module.finrank F (CyclotomicField p F))
    (hpE : 2 < Module.finrank E (CyclotomicField p E))
    {V : Type} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[p]) V]
      [Module.Finite (AlgebraicClosure ℚ_[p]) V] [Module.Free (AlgebraicClosure ℚ_[p]) V]
    (hV : Module.finrank (AlgebraicClosure ℚ_[p]) V = 2)
    (rho : GaloisRep F (AlgebraicClosure ℚ_[p]) V)
    (hrhoirred : GaloisRep.IsIrreducible (rho.map (algebraMap F E)))
    (hrhodet : ∀ g, rho.det g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
      (cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv))
    (hrhoflat : HasFlatDescentAboveEll p rho)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    (hrhounram : ∀ v ∉ S, ↑p ∉ v.asIdeal → rho.IsUnramifiedAt v)
    (hrhotame : HasGenericTameRankOneQuotient p rho S) : Prop :=
  rho.IsAutomorphicOfLevel p hp hV S →
    (rho.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S)

def SolvableBaseChangeDescent
    ⟨identical binder list⟩ : Prop :=
  (rho.map (algebraMap F E)).IsAutomorphicOfLevel p hpE hV
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S) →
    rho.IsAutomorphicOfLevel p hp hV S
```
Both elaborate with exactly-trio def audits. **`hrhoirred` is deliberately kept in both** (§5).
The admitted `cyclic_base_change` is exactly `∀ …, ForwardSolvableBaseChange … ∧
SolvableBaseChangeDescent …` modulo the single-universe restriction and the flat/tame bundle
re-packaging; consumers' scope (`E-CBASE-MLT`, `E-CBASE-BRAUER-FAMILY`) is preserved. Coefficient
/semisimplification transport stays out (all three artifacts agree it is BRAUER-owned).

---

## 4. Probe / T2 boundary / T3 proof — the three regimes (defect 5)

* **Methodology signature probe** (what this pass ran and what the buildable slice is): Lean text
  in `FLTMethodology/`, `#check`/`#print axioms` evidence, advisory only. B1–B3 land here first;
  V1–V9, Q1, Q2 land here *only* as `def`s. Per `methodology/README.md` this is not proof progress.
* **Named T2 source boundary** (requires operator authorization; this pass cannot grant it):
  two assumption rows — `ASSUME-CBASE-FORWARD` ≙ V3 and `ASSUME-CBASE-DESCENT` ≙ V4 — each tied to
  a registered, visually verified primary source. **Gate open:** `SOURCE-REGISTER.md` has no
  primary base-change row (only SRC-004, the explicitly incomplete blueprint chapter);
  Langlands is cited by name only (`KnownIn1980s.lean:39,69,90`, `blog.md:39`); Arthur–Clozel and
  any Jacquet–Langlands/multiplicity-one source have zero in-tree presence. Candidate sources the
  operator must obtain, register, and visually verify before any authorization — named here
  *without* theorem/page locators, which would be fabrication: Langlands' cyclic base-change
  monograph for GL(2); Arthur–Clozel's book on base change for GL(n); a Jacquet–Langlands source
  and a strong-multiplicity-one source for inner forms of GL(2) over totally real fields; and a
  source for the Skinner–Wiles solvable-iteration packaging. What must be visually verified: that
  the printed hypotheses cover (i) totally real solvable `E/F`, (ii) the quaternionic (not bare
  GL₂) packaging or an explicit JL bridge, (iii) the level `U₁(S)`/conductor behaviour under base
  change, (iv) the cuspidality condition governing `hρirred` placement (§5).
* **T3 standard-trio proof**: today only B1/B2a/B2b/B3. Next T3-eligible residuals, in order:
  V5's proof (Clifford-theoretic, algebraic), V9 (cyclotomic-character functoriality), Q2
  (engineering over `baseChangeAdeleContinuousAlgEquiv`), V8 at unramified `w` (Frobenius
  functoriality), V6/V7 (local Galois functoriality). Q1 is T3-eligible **only after**
  FLT-CLASS-FIELD provides Hasse–Brauer–Noether input.
* **Never proposed:** production `sorry` scaffolds. Opus's plan to land D3–D5 with `sorry` bodies
  under `FLT/GaloisRepresentation/BaseChange/Structural.lean` is rejected outright (it would mint
  new `sorryAx` production declarations, violating the exact completion test,
  `IMPLEMENTATION-PLAN.md:126ff`). The single existing admitted declaration stays where it is,
  quarantined by `ExistingAdaptersAudit.lean:116`, until authorization or proof replaces it.

---

## 5. Cuspidality / restriction-irreducibility hypothesis placement (defect 6)

`hρirred` (irreducibility of `ρ|_{G_E}`) is retained as a hypothesis of **both** V3 and V4:

* *Forward:* the only classical route to the quaternionic conclusion over `E` is
  JL⁻¹ ∘ (GL₂ base change) ∘ JL. The re-descent to the totally definite side over `E` requires the
  base-changed representation to be cuspidal; cuspidality of the base change fails exactly when the
  representation is induced from an intermediate extension, which `hρirred` excludes. On the
  repository's Galois-side packaging, reducible `ρ|_{G_E}` corresponds to eigensystems of
  norm-form-character type, which the trace conditions at good places would then have to match — a
  configuration no in-tree fact rules out.
* *Descent:* `hρirred` is the standard "not induced" precondition for the image characterization.
* *Decision rule:* no registered source resolves whether the forward direction can drop it. Until
  the operator registers and visually verifies a primary source whose forward statement is
  hypothesis-free, assigning `hρirred` to descent only (Opus counterexample 3) is **unsourced
  hypothesis-minimization** and is rejected. The conservative both-sides placement loses no
  downstream strength: both graph consumers possess `hρirred` at their call sites
  (`proof-obligations.ndjson:15,24` both carry irreducibility conditions).

Also retained in both: `hF`, `hS`, `hρdet`, `hρflat`, `hρunram`, `hρtame` — the admitted theorem
quantifies them globally and no source licenses splitting them per-direction yet. Interface Props
carry them as unused-but-present binders (linter noise accepted, exactly as the admitted theorem
does via `set_option linter.unusedVariables false`).

---

## 6. First true residuals and the missing-provider order (defect 4)

Order of the first genuine obstructions for any forward-transfer proof, established against the
kernel and the pinned API — each strictly precedes Hecke-eigensystem transport:

1. **Universe reconciliation (R1)** — type-theoretic; blocks the tensor route at elaboration time.
   Resolved by the single-universe interface (this design) or an operator decision to re-freeze.
2. **`DivisionRing (E ⊗[F] D)`** = `BaseChangeUnitsProvider` (Q1) — the **first genuinely
   mathematical missing provider**. True under the formal hypotheses (D division + rigidified ⇒
   ramified only at infinite places; `E` totally real keeps every such place real, invariants
   persist; nonempty ramification ⇒ division), but the proof *is* Hasse–Brauer–Noether local-global
   theory: absent from tree, owned by FLT-CLASS-FIELD-adjacent work, not by CBASE. No shortcut
   exists: the pinned dichotomy lemma only says "matrix algebra or division", it cannot decide
   which.
3. **`WithRigidification E (E ⊗[F] D)`** = Q2 — data construction; real support exists
   (`baseChangeAdeleContinuousAlgEquiv`, `mapRingHom` in `FiniteAdeleRing/BaseChange.lean`) but no
   adapter connects it to `M₂(𝔸ᶠ[E])`; engineering-heavy, not source-blocked.
4. **`U₁Data` transport and Frobenius compatibility** — `⟨Fact.out, S_E, ∅, 1, by simp, hpE⟩`
   assembles from B2a/B2b + `hpE`; then V8 (with inert-degree Satake bookkeeping: the E-side
   eigenvalue at `w | v` of residue degree `f` is a polynomial in the F-side `T_v`-eigenvalue and
   `N(v)`, e.g. `t_w = t_v² − 2·N(v)` for `f = 2` — an algebra-hom `T_w ↦` polynomial transport,
   *not* `T_w ↦ T_v` as the Opus artifact's "transport the Hecke system" implies).
5. Only then the analytic core (V3 content proper).

GPT's defect-6 finding ("Hecke transport is not the first residual") is therefore confirmed and
extended by items 1–2.

---

## 7. Acyclic owner graph, gates, and stop-loss

```
FLT-AUT-DEF (upstream: IsAutomorphicOfLevel; carries R2 risk)
    │
    ├──► CBASE-L0   (B1,B2a,B2b,B3; T3 now; owner FLT-CBASE)          [probe-verified]
    │        │
    ├──► CBASE-VOCAB (V1,V2,V5,V6,V7,V8,V9,Q1,Q2,V3,V4 as defs)       [probe-verified]
    │        │
    │        ├──► CBASE-GAL-FIBER (prove V5; algebraic T3 residual)
    │        ├──► QUAT-BC (prove Q2; then Q1 ◄─ FLT-CLASS-FIELD)
    │        ├──► LOCAL-TRANSPORT (prove V6,V7,V8,V9 as reachable)
    │        │
    │        ├──► ASSUME-CBASE-FORWARD (T2; operator gate; source gate OPEN)
    │        └──► ASSUME-CBASE-DESCENT (T2; operator gate; source gate OPEN;
    │                  form-level image/mult-one/JL vocabulary ◄─ FLT-JL, FLT-AUT-DEF)
    │
    └──► cyclic_base_change (admitted; later = ⟨V3-inst, V4-inst⟩; scope preserved)
             │
             ├──► FLT-MLT (absent)          [no back-edge: gate G5]
             └──► FLT-BRAUER-FAMILY (absent; +C6 coefficient transport, BRAUER-owned)
```
Acyclic by construction: no CBASE node consumes FLT-MLT, FLT-POTMOD, or any potential-automorphy
output; FLT-JL feeds descent vocabulary only.

**Source-verification gates.** G-SRC-1: no T2 authorization until a primary base-change source row
exists in `SOURCE-REGISTER.md` with visual verification of the four items in §4. G-SRC-2: any
artifact citing Langlands/Arthur–Clozel by theorem number before registration is citing from
memory — reject (both prior artifacts complied; this one does too).

**Stop-loss conditions (halt and report OBSTRUCTION if tripped).**
* G1: a proposed proof of V4 (or the iff) that does not consume form-level image/mult-one/JL
  vocabulary — hidden-axiom smell.
* G2: any production declaration with replacement `sorry`, custom axiom, `unsafe`, or
  `native_decide` in the CBASE tranche.
* G3: any route that exploits R2 (instantiating the automorphy witness with a non-totally-definite
  `D`) or drops `Even`-degree reasoning — escalate to FLT-AUT-DEF before proceeding.
* G4: any provider requiring `ULift` transport of the quaternion/Hecke stack — halt; restate at one
  universe instead.
* G5: any dependence of a CBASE node on FLT-MLT/FLT-POTMOD (cycle).
* G6: axiom audit of any landed lemma differing from exactly
  `[propext, Classical.choice, Quot.sound]`.
* G7: eigensystem-rigidity (B3) being presented anywhere as multiplicity one — statement-integrity
  violation.

---

## 8. Probe log (all disposable, `lake env lean --stdin`, no files written)

| # | Content | Result |
|---|---|---|
| P0 | `#check @cyclic_base_change` against built oleans | elaborates; two independent universes confirmed |
| P1 | B1 (corrected D1) + audit | **exactly** `[propext, Classical.choice, Quot.sound]` |
| P1′ | Opus stage-1 D1, byte-faithful | **fails**: `failed to synthesize Module ℚ F` |
| P2 | B2a + B2b + audits | both **exactly** the trio |
| P3 | B3 attempt 1 (`Algebra.adjoin_induction'`) | unknown constant (pinned Mathlib renamed it) |
| P3′ | B3 final (`Algebra.adjoin_induction`) | **exactly** the trio |
| P4 | V1, V2 (first form) | V1 clean; V2 revealed `[NumberField]` requirement of `absoluteGaloisGroup.map` |
| P4′ | V1, V2, V5, V8 (first form) | V1/V2/V5 **trio**; V8 revealed `Ideal.inertiaDeg` argument order |
| P5 | V8 fixed | **exactly** the trio |
| P6 | V6, V7, V9 | all **exactly** the trio |
| P7 | Q1, Q2 | both **exactly** the trio |
| P8 | V3, V4 full binder lists | both **exactly** the trio (unused-binder lints only) |

Every failed intermediate form is retained above as evidence; no claimed-buildable signature is
reported without a passing probe.

## 9. Execution plan for the (separately authorized) build pass

1. Create `FLTMethodology/Probes/CyclicBaseChangeBoundary.lean` containing §2 (proved) + §3 (defs),
   importing `FLT.GaloisRepresentation.Automorphic` and
   `FLTMethodology.Probes.SelectedGoodRepositoryBoundary`; `lake build` it; record `#print axioms`.
2. No edits to `FLT/` and no control-row mutations in that pass either, except as the operator
   separately authorizes: (a) optional upstream-PR of B2a/B2b/B3 into their production homes;
   (b) an FLT-AUT-DEF review item for R2 and a universe decision for R1;
   (c) `SOURCE-REGISTER.md` rows for the base-change/JL/mult-one sources, after visual check.
3. T2 authorization of `ASSUME-CBASE-FORWARD`/`ASSUME-CBASE-DESCENT` only after (c), through the
   human agreement gate; `cyclic_base_change` is then recomposed as a corollary with no scope loss.

**Verification:** each landed declaration gates on `lake build` of its module plus a per-declaration
`#print axioms` equal to the target-stage closure; the fail-closed monitor
(`methodology/control/flt_monitor.py`) remains the promotion authority; model artifacts, including
this one, are advisory.

---

**Final verdict: `DESIGN-VIABLE`** — with the two T2 source gates explicitly open, no historical
assumption authorized, and FLT-CBASE left in state `admitted`.
