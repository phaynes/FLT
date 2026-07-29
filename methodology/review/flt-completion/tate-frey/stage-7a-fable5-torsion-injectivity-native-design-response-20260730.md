# Stage 7A — Fable 5 native torsion-injectivity design response

## Evidence classification

- Model: `claude-fable-5`
- Agent: `fable5-designer-d10`
- Experimental arm: no external literature
- Duration: `1,935,991 ms`
- Claude session: `82b222cd-2c54-4809-bfef-035aad795863`
- Transcript: `/Users/philiphaynes/.claude/projects/-Volumes-second-store-devel-proof-forks-FLT-good-reduction-specialization-20260730/82b222cd-2c54-4809-bfef-035aad795863.jsonl`
- Token telemetry: input `103`; cache creation `672,810`; cache read `4,663,324`; output `284,943`; requests `55`
- Transport: success
- Content status: `IMPLEMENTABLE / DESIGN DRAFT`
- Review boundary: the model explicitly returned while its adversarial Plan-agent check remained pending. This document preserves the full drafted plan as design evidence; it is not a completed independent approval.
- Repository mutation by model: none

## Preserved drafted deliverable

# Stage 7A — Fable 5 native torsion-injectivity design (FLT-TATE-UNRAMIFIED)

Hostile-review, read-only, no-literature arm. Repo `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`, baseline `15dba9d`, HEAD `7536b82`. All file:line refs verified against this tree; kernel probe run 2026-07-30 via `lake env lean /dev/stdin` (read-only elaboration).

## 1. Verdict

**IMPLEMENTABLE.**

Every mathematical input required by the recommended route (Route D below) already exists in the
pinned snapshot with kernel-verified axiom closure exactly `[propext, Classical.choice, Quot.sound]`
(probe output reproduced in §5.2). No missing library theorem, no statement defect in the target,
no admission is inherited. What remains is genuine but purely assembly-level Lean work
(new lemmas with complete proof designs grounded in pinned API, est. 700–1200 LOC).
(Adversarial verification of the case analysis: pending Plan-agent report —§7 risk register.)

## 2. Ranked route comparison

### Route D (RECOMMENDED): division-polynomial multiplicity accounting, homomorphism-free
Injectivity is proved coordinatewise: torsion points have integral coordinates (unit leading
coefficient `n²` of `ΨSq` + valuation subrings integrally closed), so specialization computes as
`(x,y) ↦ (x̄,ȳ)`; a collision forces a root-multiplicity overflow in `ΨSq n` of the reduced curve,
bounded above via separability of `preΨ' n` (kernel-clean provider) and pointwise coprimality with
`Ψ₂Sq`. Never needs: the (unproved) hom property of `pointSpecialization`, formal groups,
completeness of `A`, `IsSepClosure`, Weil pairing, or `isCoprime_Φ_ΨSq`.
- First missing lemma: none mathematically; first NEW Lean lemma is `natCast_isUnit_of_baseRing` (§3, N1).
- Import cycles: none (§3 file split).
- Admissions in closure: none (kernel probe §5.2).
- Falsification probes: §5.3.

### Route B (REJECTED): specialization is an additive hom + kernel argument
`pointSpecialization` (GoodReduction.lean:480) is a bare function. No reduction map on points exists
anywhere in pinned Mathlib (`Reduction.lean` audited in full: only `reduction`, `IsIntegral`,
`IsMinimal`, `integralModel`, `HasGoodReduction` + trichotomy; its sole consumer, LFunction.lean,
counts points and never maps them). `Affine.Point.map` (Affine/Point.lean:784) exists only for
field-to-field algebra maps and is injective by construction — unusable as reduction. Proving
`pointSpecialization (P+Q) = pointSpecialization P + pointSpecialization Q` requires the full
valuation case analysis of the chord law degenerating mod 𝔪 (three-points-on-a-line collinearity),
strictly more work than Route D — and the kernel argument then still needs Route D's integrality
step to show kernel ∩ torsion = 0. Strictly dominated. First missing lemma:
`pointSpecialization_add` (no pinned support at any level).

### Route A (REJECTED): kernel-of-reduction / formal-parameter, no prime-to-p torsion in Ê(𝔪)
Triple-blocked.
(i) Mathematically inaccurate definition in the only formal-group multiplication available:
vendored `formalMulByInt_coeff` (vendor/HasseWeil/FormalGroup/FormalGroupAssoc.lean:97-106) is
documented wrong for `m < 0`, `n ≥ 2` ("For simplicity, we use |m| here; … This is a
simplification."). Correction 4 forbids inheriting it.
(ii) Structural emptiness: no group structure `Ê(𝔪)` exists in vendor (the promised
`HasseWeil.FormalGroup.add/.neg/.mulByInt` are docstring-only; `formalGroupEval` is a truncated sum
with no group axioms) nor in Mathlib (`RingTheory/FormalGroup/Basic.lean`: `F.Point σ` is only an
`AddMonoid`, no inverse series, no `[n]`, explicit TODO at :122-124 for the maximal-ideal case).
No filtration `Ê(𝔪ⁿ)`, no `[m]`-injectivity, no reduction map to identify the kernel with `Ê(𝔪)`.
(iii) Statement-level obstruction: the target's `A` is an arbitrary valuation subring of `ksep`
lying over `R` — non-noetherian value group, NOT complete. Evaluating `[n](T) ∈ A⟦T⟧` at `t ∈ 𝔪_A`
requires adic convergence; a completion-and-transport layer has no pinned support. First missing
lemma: `Ê(𝔪)` group instance (Silverman IV.3.2 stack ≈ thousands of LOC), plus a completeness
bridge that is false to state for `A` itself.

### Route C (REJECTED as stated / absorbed into D): "coprimality + discriminant of ΨSq"
The in-source sketch (Flat.lean:190-202) suggests `isCoprime_Φ_ΨSq` plus "a companion identity for
the discriminant of `ΨSq n` (of the same `±nᵃ * Δᵇ` shape)". Defect: for odd `n`,
`ΨSq n = (preΨ' n)²` exactly (Mathlib `ΨSq_ofNat`, DivisionPolynomial/Basic.lean:246), so
`disc(ΨSq n) ≡ 0` identically; for even `n`, `ΨSq n = (preΨ' n)²·Ψ₂Sq`, also inseparable. The
correct object is `disc(preΨ' n)` — i.e. exactly the separability input Route D consumes through
the already-proved `prePsi_separable`. Coprimality `Φ/ΨSq` alone cannot separate `P` from `−P`
(same `x`), nor two distinct points colliding mod 𝔪 (Correction 3). Also note: kernel probe shows
`isCoprime_Φ_ΨSq` audits clean — the repo's own `DivisionPolynomialCoprimeAudit.lean` docstring
hedge ("remaining dependency on the admitted division-polynomial resultant identity") is stale;
`resultant_Φ_ΨSq` (Flat.lean:251, sorry) is NOT in its closure. Route D does not use it either way.

### Route E (SEPARATE OPTION, not closure of the generic target): consumer-specialized theorem
Consumer evidence: zero Lean call sites for the target. Intended consumer
`FreyCurve.torsion_isHardlyRamified` (FLT/GaloisRepresentation/HardlyRamified/Frey.lean:52, itself
sorry) needs only: `n = P.p` an ODD PRIME ≥ 5, base ℚ_p at primes `p ∉ {2, ℓ}`, one fixed embedding
`𝒪`. Quantified difference from the generic target: (a) even `n` — unneeded (kills the entire
`Ψ₂Sq`/step-4b branch); (b) `n` composite — unneeded; (c) arbitrary DVR/valuation subring —
consumer fixes `ℤ_p`-shaped `R` and one `𝒪`; (d) the consumer additionally needs two lemmas the
generic theorem does NOT provide: `HasGoodReduction` instantiation for the Frey curve away from
`2ℓ`, and the documented local→global torsion/inertia transport bridge
(FLT-TATE-FLAT-CONSUMER-SLICE.md:24-28) — neither is part of this obligation. An odd-prime-only
InjOn theorem would shrink Route D's case analysis by ~40% but closes a different statement; per
the stage rules it may only be built as a separate declaration, never presented as closing the
unchanged generic target. Not recommended: Route D's even-`n` cost is modest because
`NeZero (n : κ(R))` + even `n` already forces residue char ≠ 2.

## 3. Proposed Lean signatures in dependency order

Context abbreviations (all in the target's variable context, GoodReduction.lean:543-561):
`κA := IsLocalRing.ResidueField A`, `resA := algebraMap A κA`,
`Ẽ := (E.reduction R).map (A.baseResidueMap R k hA)`,
`EA := A.extendedIntegralModel R k E hA`, `E' := E.map (algebraMap k ksep)`.

FILE SPLIT (no cycles): new generic lemmas that never mention `pointSpecialization` go in
- `FLT/EllipticCurve/TorsionProof/RootMultiplicityBounds.lean` (imports Mathlib + PsiSqExactDetection + TorsionParityCount + PrePsiTwoTorsion + TorsionProvider), and
- `FLT/Mathlib/RingTheory/Valuation/IntegralRoots.lean` (generic valuation/polynomial lemmas, Mathlib-only imports).
The `pointSpecialization`-facing lemmas and the final assembly go INTO GoodReduction.lean itself,
which gains `public import` of the two files above (verified: no TorsionProof/TorsionProvider file
imports GoodReduction — direction is acyclic). GoodReduction.lean uses `module`/`public import`
conventions; new files must too. [Pending verifier confirmation of split viability.]

### Existing declarations consumed (no change, kernel-audited where marked ✓K)
- `FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero` — PsiSqExactDetection.lean:45 ✓K
- `FLT.EllipticCurve.TorsionProvider.prePsi_separable` — TorsionProvider.lean:47 ✓K (closure includes admission-free vendor slice; `formalMulByInt` statements used only at coeff indices ≤ 1)
- `FLTMethodology.Torsion.prePsi_pointwise_coprime` — PrePsiTwoTorsion.lean:228 ✓K
- `FLTMethodology.Torsion.psiTwoSq_separable` — TorsionParityCount.lean:82 ✓K (`(2:k) ≠ 0`)
- `FLTMethodology.Torsion.psiTwoSq_eval_eq_fiber_discriminant` — TorsionParityCount.lean:115 ✓K
- Mathlib: `ΨSq_ofNat` (DivPoly/Basic.lean:246), `map_ΨSq` (:522), `leadingCoeff_ΨSq`/`natDegree_ΨSq` (Degree.lean:370/361), `ΨSq_ne_zero` (:374), `eq_rootMultiplicity_map` (Roots.lean:906), `le_rootMultiplicity_map` (:900), `rootMultiplicity_mul` (RingDivision.lean:291), `rootMultiplicity_le_one_of_separable` (Separable.lean:275), `map_modByMonic`/`map_divByMonic` (Div.lean:395/391), `IsFractionRing A K` (ValuationSubring.lean:153), `IsIntegrallyClosed V` (LocalSubring.lean:38), `Affine.Point.neg_some` (:627), `eq_or_eq_neg_of_xRep_eq_xRep` (:870), `Projective.equiv_iff_eq_of_Z_eq` (Projective/Basic.lean:175), `not_equiv_of_Z_eq_zero_left` (:193), `IsLocalRing.residue_ne_zero_iff_isUnit` (used at GoodReduction.lean:173)
- Repo prefix (all proved): `baseRingHom`, `baseResidueMap`, `extendedIntegralModel`, `map_extendedIntegralModel_eq`, `residue_extendedIntegralModel_eq`, `residueRepresentative_of_ne_zero`, `residue_pointClass_eq_of_scaled`, `projectiveResidue_mk`, `pointSpecialization`, `pointSpecialization_inertia`, `torsion_fixed_of_invariant_injective`

### NEW declarations

**File FLT/Mathlib/RingTheory/Valuation/IntegralRoots.lean** (generic; Mathlib-only imports)

```lean
-- N0. root of a unit-leading-coeff A-polynomial lies in A
theorem ValuationSubring.mem_of_aeval_eq_zero_of_isUnit_leadingCoeff
    {F : Type*} [Field F] (A : ValuationSubring F) {p : Polynomial A}
    (hu : IsUnit p.leadingCoeff) {x : F}
    (hx : Polynomial.aeval x p = 0) : x ∈ A

-- N3a. single-root multiplicity descent to the residue field
theorem ValuationSubring.rootMultiplicity_residue_le
    {F : Type*} [Field F] (A : ValuationSubring F) {p : Polynomial A}
    (hp : p.map (algebraMap A F) ≠ 0) (x : A) :
    Polynomial.rootMultiplicity (x : F) (p.map (algebraMap A F)) ≤
      Polynomial.rootMultiplicity (algebraMap A (IsLocalRing.ResidueField A) x)
        (p.map (algebraMap A (IsLocalRing.ResidueField A)))

-- N3b. two colliding roots add their multiplicities
theorem ValuationSubring.rootMultiplicity_residue_add_le
    {F : Type*} [Field F] (A : ValuationSubring F) {p : Polynomial A}
    (hp : p.map (algebraMap A F) ≠ 0) {x₁ x₂ : A} (hx : x₁ ≠ x₂)
    (hres : algebraMap A (IsLocalRing.ResidueField A) x₁ =
            algebraMap A (IsLocalRing.ResidueField A) x₂) :
    Polynomial.rootMultiplicity (x₁ : F) (p.map (algebraMap A F)) +
      Polynomial.rootMultiplicity (x₂ : F) (p.map (algebraMap A F)) ≤
      Polynomial.rootMultiplicity (algebraMap A (IsLocalRing.ResidueField A) x₁)
        (p.map (algebraMap A (IsLocalRing.ResidueField A)))
```
Proof design N3: `D := (X − C x₁)^m₁ * (X − C x₂)^m₂` monic in `A[X]`; divisibility of the maps by
`pow_rootMultiplicity_dvd` + coprimality of distinct linear factors; descend `D ∣ p` to `A[X]` via
`map_modByMonic` + injectivity of `A.subtype`; push through `resA`; conclude by the
`(X−a)^m ∣ q → m ≤ rootMultiplicity` direction (`le_rootMultiplicity_iff`). Note residue map need
NOT be injective — descent happens in `A[X]` first, exactly why the lemma is stated with `p : A[X]`.

**File FLT/EllipticCurve/TorsionProof/RootMultiplicityBounds.lean** (generic curve lemmas over any field K)

```lean
-- N4. 2-torsion y-criterion as a square identity  (K any field, W : WeierstrassCurve K)
theorem FLTMethodology.Torsion.psiTwoSq_eval_eq_sq_of_equation
    {K : Type*} [Field K] (W : WeierstrassCurve K) {x y : K}
    (hE : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2

-- N5. gcd elimination (pure ℤ-module algebra; may exist — verifier searching)
theorem AddSubgroup.eq_zero_of_torsionBy_coprime
    {G : Type*} [AddCommGroup G] {P : G} {m n : ℤ}
    (hm : m • P = 0) (hn : n • P = 0) (h : IsCoprime m n) : P = 0

-- N6. upper bounds over any field with separable preΨ'  (n : ℕ)
theorem FLTMethodology.Torsion.rootMultiplicity_psiSq_le_two
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) (hsep : (W.preΨ' n).Separable) (x : K) :
    ((W.ΨSq (n : ℤ)).rootMultiplicity x) ≤ 2

theorem FLTMethodology.Torsion.rootMultiplicity_psiSq_le_one_of_psiTwoSq_root
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) (heven : Even n) (hsep : (W.preΨ' n).Separable)
    {x : K} (hx : W.Ψ₂Sq.eval x = 0) :
    ((W.ΨSq (n : ℤ)).rootMultiplicity x) ≤ 1

-- N7. lower bound over the source field (dictionary side)
theorem FLTMethodology.Torsion.two_le_rootMultiplicity_psiSq_of_not_two_torsion
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] [DecidableEq K]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K} (h : W.toAffine.Nonsingular x y)
    (htor : (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h) = 0)
    (h2 : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    2 ≤ (W.ΨSq (n : ℤ)).rootMultiplicity x
```

**Additions to FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean** (specialization-facing; same
variable context as the target)

```lean
-- N1. n is a unit in A
theorem ValuationSubring.natCast_isUnit_of_baseRing
    (A : ValuationSubring ksep) (hA : …) (n : ℕ)
    [NeZero (n : IsLocalRing.ResidueField R)] : IsUnit (n : A)
-- corollaries: (n : ksep) ≠ 0, (n : k) ≠ 0, (n : IsLocalRing.ResidueField A) ≠ 0

-- N2. torsion coordinates are integral
theorem ValuationSubring.torsion_point_coords_mem
    (A : ValuationSubring ksep) (E : WeierstrassCurve k) [E.IsElliptic] [E.IsMinimal R]
    (hA : …) (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] [DecidableEq ksep]
    {x y : ksep} (h : (E'.toAffine).Nonsingular x y)
    (htor : (n : ℤ) • (WeierstrassCurve.Affine.Point.some x y h) = 0) :
    x ∈ A ∧ y ∈ A

-- N8. specialization computes coordinatewise on integral affine points
theorem ValuationSubring.pointSpecialization_some_point_eq
    … {x y : ksep} (hx : x ∈ A) (hy : y ∈ A) (h : …Nonsingular x y) :
    (A.pointSpecialization R k E hA (.some x y h)).point =
      (⟦![resA ⟨x, hx⟩, resA ⟨y, hy⟩, 1]⟧ : WeierstrassCurve.Projective.PointClass κA)

-- N9. specialization of zero
theorem ValuationSubring.pointSpecialization_zero_point_eq
    … : (A.pointSpecialization R k E hA 0).point = (⟦![0, 1, 0]⟧ : …PointClass κA)

-- N10. reduced coordinates satisfy the reduced curve's affine equation + nonsingularity
theorem ValuationSubring.reduced_torsion_nonsingular
    … (hx : x ∈ A) (hy : y ∈ A) (h : …) :
    Ẽ.toAffine.Nonsingular (resA ⟨x,hx⟩) (resA ⟨y,hy⟩)

-- N11. THE LEAF
theorem ValuationSubring.pointSpecialization_injOn_torsion
    (A : ValuationSubring ksep)
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R] [DecidableEq ksep]
    (hA : (A.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] :
    Set.InjOn (A.pointSpecialization R k E hA)
      (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))

-- N12. close the target (replace the sorry at GoodReduction.lean:574) via
-- torsion_fixed_of_invariant_injective E n (fun σ : 𝒪.decompositionSubgroup k ↦ (σ : ksep ≃ₐ[k] ksep))
--   {σ | σ ∈ 𝒪.inertiaSubgroup k} (𝒪.pointSpecialization R k E h𝒪)
--   (𝒪.pointSpecialization_injOn_torsion …) (fun σ hσ P _ ↦ 𝒪.pointSpecialization_inertia … σ hσ P)
```

Case analysis of N11 (complete enumeration; verifier attacking): (0,0) refl; (0,some)/(some,0)
killed by N8/N9 + `not_equiv_of_Z_eq_zero_left`; (some,some) with N2 integrality and N8 giving
`x̄₁ = x̄₂, ȳ₁ = ȳ₂` via `equiv_iff_eq_of_Z_eq`; then
- `x₁ = x₂`: `eq_or_eq_neg_of_xRep_eq_xRep` ⇒ `P = Q` (done) or `Q = −P` with `P ≠ −P`;
  then `2ȳ₁+ā₁x̄₁+ā₃ = 0`. Odd `n`: reduced point is affine, `n`-torsion (dictionary over κA,
  `Classical.decEq`), 2-torsion (`neg_some`), N5 with `IsCoprime 2 n` ⇒ point `= 0`, absurd.
  Even `n`: N7+N3a give `mult ≥ 2`; N4+N6b give `mult ≤ 1`; absurd.
- `x₁ ≠ x₂`: N3b gives `m₁ + m₂ ≤ mult_{x̄}(ΨSq Ẽ)`. Both non-2-torsion: `4 ≤ mult ≤ 2` (N6a) absurd.
  Mixed (even `n`): `3 ≤ mult ≤ 2` absurd; odd `n`: nonzero 2-torsion ∧ n-torsion over ksep already
  absurd by N5. Both 2-torsion (even `n`): `2 ≤ mult ≤ 1` (N4 reduces, N6b) absurd.
Degenerate `n`: `n = 0` excluded by `NeZero`; `n = 1`: dictionary makes the some-branch hypotheses
contradictory (`ΨSq 1 = 1`); `n = 2`: `Q = −P` with both 2-torsion forces `Q = P` — branch closes
in the `P = Q` disjunct. Characteristic safety: odd-`n` branches never touch `Ψ₂Sq`
separability/(2:κ)≠0 (char-2-safe); even `n` + `NeZero (n : κ(R))` forces residue char ≠ 2 and
char k ≠ 2; nothing anywhere uses char ≠ 3, completeness, discreteness of `A`, or `IsSepClosure`.

## 4. Smallest honest kernel-green build tranche

Tranche T1 (no assumption added, no target-equivalent contract, each item independently valuable):
1. `IntegralRoots.lean`: N0, N3a, N3b (generic; Mathlib-only imports).
2. `RootMultiplicityBounds.lean`: N4, N5, N6a, N6b, N7.
3. GoodReduction.lean additions: N1, N2, N8, N9, N10 (prefix-compatible, no restatement of the
   target; the sorry at :574 stays untouched in T1).
Everything in T1 has hypotheses strictly weaker than or equal to the target's own; nothing is
equivalent to the leaf (the leaf's content is the N11 case analysis, deliberately excluded from T1).
Tranche T2 = N11 + N12 (closes the leaf and the target).

## 5. Required builds, audits, negative controls, stop-loss

### 5.1 Direct builds (per repo precedent, stage-5 record)
- `lake env lean FLT/Mathlib/RingTheory/Valuation/IntegralRoots.lean` and each new/changed file;
- narrow build of the GoodReduction target set (~2,505 jobs); `lake -H build FLT FLTMethodology`
  (~9,047 jobs); `git diff --check`; added-line prohibited-token scan (`warn.sorry = false` in
  lakefile ⇒ grep is mandatory, build warnings are NOT evidence).

### 5.2 Axiom audits (executable; kernel evidence, not elaboration evidence)
Already captured this stage (must be re-run and re-captured in the build stage):
```
'FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero' : [propext, Classical.choice, Quot.sound]
'FLT.EllipticCurve.TorsionProvider.prePsi_separable'          : [propext, Classical.choice, Quot.sound]
'FLT.EllipticCurve.TorsionProvider.nTorsion_card_sepClosed'   : [propext, Classical.choice, Quot.sound]
'HasseWeil.WeilPairing.TorsionGeometric.card_torsion_ell'     : [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.isCoprime_Φ_ΨSq'                            : [propext, Classical.choice, Quot.sound]
'FLTMethodology.Torsion.prePsi_pointwise_coprime'             : [propext, Classical.choice, Quot.sound]
'FLTMethodology.Torsion.psiTwoSq_separable'                   : [propext, Classical.choice, Quot.sound]
'FLTMethodology.Torsion.psiTwoSq_eval_eq_fiber_discriminant'  : [propext, Classical.choice, Quot.sound]
```
Per new declaration: `#print axioms` must be exactly `[propext, Classical.choice, Quot.sound]`
(T1 policy allows `knownin1980s` but nothing here needs it). After T2: unchanged-target audit of
`torsion_unramified_of_good_reduction` must show `sorryAx` GONE. Additional statement-level audit:
grep the closure of `prePsi_separable` for `formalMulByInt` uses at coefficient index ≥ 2
(agent-audited: only indices ≤ 1 are used; re-verify mechanically).

### 5.3 Negative controls (repo idiom: wrong-inhabitant def + positive refutation + #print axioms, in FLTMethodology/Probes/)
- `PsiSqNotSeparableProbe.lean`: for `W` over `ℚ`, prove `¬ (W.ΨSq 3).Squarefree` via
  `ΨSq_three : ΨSq 3 = Ψ₃ ^ 2` + `natDegree_Ψ₃ = 4` — executable refutation of any
  "ΨSq separable/discriminant" design (Correction 2 control; kills the Flat.lean:190-202 sketch).
- `XCoordinateInsufficiencyProbe.lean`: exhibit `P ≠ −P` with `(−P).xRep = P.xRep` (`xRep_neg`) —
  refutes any x-only reduction codomain (stage-4 rejection, Correction 3 control).
- `EvenTorsionCharTwoProbe.lean`: `(2 : ZMod 2) = 0` ⇒ no instance
  `NeZero ((2:ℕ) : ZMod 2)` — records that even `n` at residue char 2 is excluded by the target's
  OWN hypothesis, not silently by the design.
- Architectural control: new files' import closure must not mention
  `IsAdicComplete`/`UniformSpace`-completion or `IsSepClosure` (the design must not smuggle
  completeness/separable-closure assumptions; checked by import grep).

### 5.4 Stop-loss
If N3 (multiplicity descent) or the N11 case analysis fails to elaborate within the bounded build:
keep every already-green T1 declaration (each is independently meaningful), reclassify the residual
precisely as "N11 case analysis" (NOT as a new opaque contract), and split it as a standalone
obligation. Never restate the leaf as a hypothesis, structure field, or `Prop`-valued contract;
never touch the target's sorry unless N11+N12 are fully green. If the `prePsi_separable` re-audit
ever shows a non-standard axiom (not expected), demote Route D's N6 to a NAMED LEAF
(`Separable (Ẽ.preΨ' n)`) and the verdict to IMPLEMENTABLE-AFTER-NAMED-LEAVES.

## 6. Exact claim remaining open after Tranche T1

```lean
Set.InjOn (A.pointSpecialization R k E hA)
  (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))
```
under `[NeZero (n : IsLocalRing.ResidueField R)]` — i.e. exactly N11 (and its one-line consumer
N12). After T2, nothing remains open in this obligation; downstream, `FLT-TATE-UNRAMIFIED`'s
consumer still needs the separate (out-of-scope) Frey `HasGoodReduction` instantiation and the
local→global transport bridge documented at FLT-TATE-FLAT-CONSUMER-SLICE.md:24-28.

## 7. Risk register / pending verification

- [PENDING] Adversarial Plan-agent verification of: `(E.map f).IsElliptic` instance availability;
  `Affine.map_equation`/`equation_iff_nonsingular` route for N10; `AddSubgroup.torsionBy` source
  (Mathlib vs FLT/Mathlib) and its `nsmul_iff`; exact `Monic → (q ∣ p ↔ p %ₘ q = 0)` name;
  glue typecheck of N12; file-split cycle check; N5 existence in Mathlib.
- Verified this stage: dictionary closure (32 files, zero admissions, zero vendor); vendor slice
  (zero executable admissions; 7 stale docstrings — documentation finding; `formalMulByInt`
  defect quarantined to indices ≥ 2 / negative m, unused); kernel probe §5.2; consumer evidence;
  T1 axiom policy `{propext, Classical.choice, Quot.sound}` (+`knownin1980s` allowed, unused).
- Honest-evidence discipline: no elaboration, contract, or docstring counts as proof; only
  `#print axioms` output and kernel-checked builds.

