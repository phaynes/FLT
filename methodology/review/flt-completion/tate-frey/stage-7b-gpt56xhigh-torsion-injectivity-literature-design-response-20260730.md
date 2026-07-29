# Stage 7B — GPT-5.6 xhigh literature-anchored torsion-injectivity design response

## Evidence classification

- Model: `gpt-5.6-sol`
- Effort: `xhigh`
- Agent: `gpt56xhigh-designer-d10`
- Experimental arm: literature anchored
- Duration: `1,403,500 ms`
- Codex session: `019fafc3-b19a-7492-a416-2a8665ecdaa1`
- Transcript: `/Users/philiphaynes/.codex/sessions/2026/07/30/rollout-2026-07-30T07-24-25-019fafc3-b19a-7492-a416-2a8665ecdaa1.jsonl`
- Token telemetry: input `13,480,310`; cached input `12,996,352`; output `66,630`; reasoning output `25,372`; total `13,546,940`
- Verdict: `IMPLEMENTABLE-AFTER-NAMED-LEAVES`
- Repository mutation by model: none

## Preserved response

IMPLEMENTABLE-AFTER-NAMED-LEAVES

The generic theorem is mathematically sound over the stated arbitrary valuation subring, including noncomplete and nondiscrete cases. The smallest route does not need formal-series evaluation or a completeness assumption: use the existing exact `ΨSq` torsion detector to prove that every nonzero prime-to-residue-characteristic torsion point has integral affine coordinates, hence cannot specialize to infinity. The remaining geometric leaf is compatibility of specialization with subtraction—or, more conventionally, additivity.

No repository or Helios state was changed.

## 1. Frozen-boundary findings

- Checkout is clean on `codex/ca-flt-good-reduction-specialization-20260730`.
- Current HEAD is `7536b82`, not the reviewed `15dba9d`; the only delta is the two Stage 7 prompt Markdown files. No Lean source differs.
- Direct elaboration of [GoodReduction.lean](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean:480) passes, with the unchanged target’s `sorry` warning at [line 568](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean:568).
- `pointSpecialization`, `pointSpecialization_inertia`, and `torsion_fixed_of_invariant_injective` each audit to exactly:
  `[propext, Classical.choice, Quot.sound]`.
- The exact dictionary in [PsiSqExactDetection.lean](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/EllipticCurve/TorsionProof/PsiSqExactDetection.lean:45) builds and has the same standard axiom trio.
- Its import path is:

```text
PsiSqExactDetection
  → PsiSqAllCharacteristic
  → KummerProjectivePropagation
  → KummerAddSubPoint
  → PrePsiWindowSteps
      → EllipticTorsionSourceBoundary
      → PrePsiWindowAlgebra
```

This path has no `Flat`, `GoodReduction`, or vendored-formal-group dependency and no executable `sorry`/`admit`/custom axiom in the checked files.

One small elaboration correction is needed when the open leaf is tested outside its original prose context. The displayed form does not infer the `AddSubgroup → Set` coercion in this snapshot. This elaborates:

```lean
Set.InjOn (A.pointSpecialization R k E hA)
  ((AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ) :
      AddSubgroup (E⁄ksep).Point) :
    Set (E⁄ksep).Point)
```

A conditional stdin proof that this corrected injectivity statement closes the existing target through `torsion_fixed_of_invariant_injective` and `pointSpecialization_inertia` passed with no `sorry`.

## 2. Source-to-Lean proof map

The literature corpus supports the following mathematics, but does not itself constitute proof evidence.

| Mathematical step | Source support | Present Lean status |
|---|---|---|
| Reduction kernel at \(O\) is the first formal-group neighbourhood | Advanced Topics cites AEC VII.2.1–2.2 and records \(P=(x,y)\mapsto -x/y\): [SRC-024:17916](/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd:17916). | `pointSpecialization` exists, but no additive-hom/kernel packaging or curve-to-formal-group equivalence exists. |
| The reduction kernel contains no prime-to-residue-characteristic torsion | Advanced Topics explicitly cites AEC VII.3.1(a)/(b): [5688](/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd:5688), [6164](/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd:6164), [15214](/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd:15214). | Not yet packaged for `pointSpecialization`. |
| \([n](T)=nT+\text{higher terms}\) | The vendored formal-group comments attribute the linear coefficient to AEC IV.2.3(a). | Abstract power-series algebra exists; the target curve/kernel correspondence does not. |
| Unit \(n\) preserves the leading term | Elementary local-ring algebra; implementation inference, not an additional literature theorem. | A complete stdin Lean proof was checked. |
| No nonzero \(n\)-torsion in the kernel | Consequence of the previous two steps. | General algebraic elimination lemma was checked; geometric parameter bridge remains absent. |
| Reduction is injective on \(n\)-torsion | AEC VII.3.1(b), cited repeatedly in the available volume. | Follows from a zero-fibre theorem plus subtraction compatibility. |
| Inertia fixes torsion | Existing Stage 6 prefix plus injectivity. | Conditional closure checked. |

The source gap is exact: the available Advanced Topics volume cites AEC VII.2.2 and VII.3.1 but does not contain the complete first-volume proof. It cannot support invented quotations or a claimed formal proof of those results.

### Completeness question

The proof can be algebraic over arbitrary `A : ValuationSubring ksep`.

A finite first-order formal-parameter proof only needs

```text
t(n • P) = n * t(P) + t(P)^2 * c
```

for some `c : A`. If `t(P)` is in the maximal ideal and `n` is a unit, then `n + t(P)c` is a unit, so

```text
0 = t(P) * (n + t(P)c)
```

forces `t(P)=0` in the domain `A`. No infinite power-series evaluation is necessary.

By contrast, [Associated.lean](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/AINTLIB/projects/HasseWeil/HasseWeil/FormalGroup/Associated.lean:719) transports the series theorem to elements only under linear-topology, Hausdorff, completeness, and adic hypotheses. Those cannot be silently installed on an arbitrary valuation subring of `ksep`; such rings may be noncomplete and may have nondiscrete value group. That route would weaken the theorem.

## 3. Ranked routes

### 1. Integral coordinates plus weak subtraction compatibility — recommended

Use the exact torsion dictionary and `leadingCoeff_ΨSq = n²`.

For an affine torsion point `(x,y)`:

1. `ΨSq n` vanishes at `x`.
2. Over the extended integral model, its leading coefficient is a unit.
3. Rescaling gives a monic polynomial over `A` with root `x`.
4. Since a valuation subring is integrally closed in its fraction field, `x ∈ A`.
5. The Weierstrass equation is monic in `y`, so `y ∈ A`.
6. `[x:y:1]` reduces with last coordinate `1`, hence not to infinity.

The `x ∈ A` and `y ∈ A` proofs were fully elaborated through stdin and each audited to the standard axiom trio. This is stronger evidence than signature elaboration, but it is not a repository change or completion claim.

First post-tranche missing mathematical lemma:

```lean
theorem ValuationSubring.pointSpecialization_sub_eq_zero_of_eq
    (P Q : (E⁄ksep).Point)
    (hPQ :
      A.pointSpecialization R k E hA P =
      A.pointSpecialization R k E hA Q) :
    A.pointSpecialization R k E hA (P - Q) = 0
```

This is weaker than full additivity and sufficient. It does not contain torsion, `n`, injectivity, or the target theorem.

Admission closure: the proposed tranche needs only `GoodReduction`’s reviewed declarations plus the clean exact-detection graph. It does not depend on the admitted target.

Fast falsification probes:

- Remove `[NeZero (n : ResidueField R)]`: construction of the unit leading coefficient must fail.
- Take residue characteristic `2` and even `n`: the `NeZero` instance must be impossible.
- Retain residue characteristic `2` with odd `n`, or characteristic `3` with `3 ∤ n`: the proof must still elaborate because it divides by neither `2` nor `3`.
- Check an affine integral point reduces with projective `Z=1`; if it can equal zero, the normalization bridge is defective.
- Scan the resulting signatures for `CompleteSpace`, `T2Space`, `IsAdic`, `Odd n`, or `NeZero (2 : ...)`; any occurrence is a stop condition.

### 2. Full additivity followed by a kernel theorem

First missing lemma:

```lean
theorem ValuationSubring.pointSpecialization_add
    (P Q : (E⁄ksep).Point) :
    A.pointSpecialization R k E hA (P + Q) =
      A.pointSpecialization R k E hA P +
      A.pointSpecialization R k E hA Q
```

Together with `pointSpecialization_zero`, this packages:

```lean
noncomputable def ValuationSubring.pointSpecializationHom :
    (E⁄ksep).Point →+
      ((E.reduction R).map (A.baseResidueMap R k hA)).toProjective.Point
```

This is source-faithful and reusable, but proving every projective addition branch—including infinity, inverse points, doubling, and characteristics two and three—is probably larger than the weak subtraction lemma.

Fast probe: separately elaborate zero/zero, zero/affine, affine/inverse, affine/doubling, and generic affine/affine cases. Failure confined to one branch should not trigger replacement of the reviewed specialization construction.

### 3. Algebraic formal-parameter route

The correct new interfaces would be:

```lean
noncomputable def SpecializationKernel.parameter
    (P : (A.pointSpecializationHom R k E hA).ker) : A

theorem SpecializationKernel.parameter_mem_maximalIdeal
    (P : (A.pointSpecializationHom R k E hA).ker) :
    P.parameter ∈ IsLocalRing.maximalIdeal A

theorem SpecializationKernel.parameter_eq_zero_iff
    (P : (A.pointSpecializationHom R k E hA).ker) :
    P.parameter = 0 ↔ P = 0

theorem SpecializationKernel.parameter_nsmul_linear
    (m : ℕ) (P : (A.pointSpecializationHom R k E hA).ker) :
    ∃ c : A,
      (m • P).parameter =
        (m : A) * P.parameter + P.parameter ^ 2 * c
```

The last declaration is the first genuinely missing formal-group/curve lemma. It expresses a first-order congruence, not an infinite evaluation.

Reusable clean algebra:

- [Hom.lean:539](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/AINTLIB/projects/HasseWeil/HasseWeil/FormalGroup/Hom.lean:539) proves series-level injectivity when `n` is a unit.
- The legacy linear-coefficient declarations audit cleanly.

Excluded material:

- [FormalGroupAssoc.lean:92](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/AINTLIB/projects/HasseWeil/HasseWeil/FormalGroup/FormalGroupAssoc.lean:92) explicitly uses `natAbs` for higher coefficients at negative indices and documents the missing inverse-composition correction.
- [FormalGroupCorrespondence.lean:355](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/AINTLIB/projects/HasseWeil/HasseWeil/FormalGroup/FormalGroupCorrespondence.lean:355) only restates the linear coefficient; it is not a point/kernel correspondence.
- The broader AINTLIB curve/isogeny formal-series source contains admitted correspondence leaves, including `FormalSeries.lean`.
- `Associated.lean` could not be directly elaborated because the required new abstract `EvalGroup.olean` is not built in this worktree. Even if built, its topology assumptions do not match the target.

Verdict: mathematically viable algebraically, but a larger construction than route 1. Completion-based evaluation is rejected.

### 4. Corrected division-polynomial direct injectivity

`ΨSq` is defined as

```lean
preΨ n ^ 2 * if Even n then Ψ₂Sq else 1
```

in [DivisionPolynomial/Basic.lean:241](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:241). Thus its ordinary discriminant is generically zero; it cannot provide distinct roots.

The appropriate reduced factor is:

```lean
def torsionXSquarefreeFactor
    (W : WeierstrassCurve F) (n : ℕ) : F[X] :=
  W.preΨ' n * if Even n then W.Ψ₂Sq else 1
```

Useful declarations already exist and audit to the standard trio:

- `FLT.EllipticCurve.TorsionProvider.prePsi_separable`;
- `FLTMethodology.Torsion.prePsi_pointwise_coprime`;
- `FLTMethodology.Torsion.psiTwoSq_separable`;
- the exact `ΨSq` torsion dictionary.

The first missing general lemma is a root-reduction separation theorem for an integral polynomial whose residue polynomial is separable. It must then be paired with:

- non-two-torsion y-fibre separation using `Ψ₂Sq(x) ≠ 0`;
- the unique two-torsion fibre when `n` is even;
- a distinct explicit infinity case.

`isCoprime_Φ_ΨSq` at [Flat.lean:260](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/KnownIn1980s/EllipticCurves/Flat.lean:260) only says the two Kummer coordinates do not vanish simultaneously. It does not distinguish `P` from `-P`, solve y-coordinate collisions, or handle even torsion.

Two comments in [Flat.lean](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/KnownIn1980s/EllipticCurves/Flat.lean:167) should eventually be corrected:

- Lines 170–173 are stale: the exact torsion dictionary now exists.
- Lines 193–198 must refer to separability of the squarefree factor above and y-fibre separation, not a discriminant of `ΨSq`.

Verdict: viable but strictly larger than the zero-fibre route.

### 5. Finite-étale/scheme route

AINTLIB contains the strong infinitesimal theorem [Point.eq_zero_of_killed_restrict](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/.lake/packages/AINTLIB/projects/ModularCurves/ModularCurves/EllipticCurve/TorsionUnramifiedFibre.lean:1294). Its first missing bridge into this target is essentially:

```lean
noncomputable def WeierstrassCurve.toSchemeModel
    (W : WeierstrassCurve A) [W.IsElliptic] :
    ModularCurves.EllipticCurve (Spec (CommRingCat.of A))
```

followed by point and reduction equivalences.

This is a different curve and point API. Moreover, its torsion import path contains admitted quasi-finiteness, flatness, and degree declarations in `ModularCurves/EllipticCurve/Torsion.lean`. The clean augmentation lemma cannot by itself cross the absent model/point bridge.

Verdict: rejected for this tranche.

### 6. Odd-prime FLT consumer specialization

The eventual Frey consumer uses `ℓ = P.p`, known prime and odd, while `IsHardlyRamified.isUnramified` only asks about primes `q ≠ 2, ℓ`: [Frey.lean:52](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/GaloisRepresentation/HardlyRamified/Frey.lean:52), [Defs.lean:96](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96). The blueprint uses good reduction only when `q ∤ abc`: [ch03freyold.tex:208](/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730/blueprint/src/chapter/ch03freyold.tex:208).

This specialization removes:

- even `n`;
- residue characteristic two;
- the even division-polynomial factor.

It does not remove characteristic three and does not simplify the formal-kernel argument. More importantly, the repository still has no local-separable-closure/global-`AbsoluteTorsion` transport, and no current Lean consumer calls the generic theorem.

Therefore an odd-prime theorem is a legitimate separate division-polynomial experiment, not closure of the generic target and not currently a directly consumable replacement.

## 4. Dependency-ordered interfaces

Using the existing Stage 6 context, the preferred interface order is:

```lean
-- EXISTING
ValuationSubring.baseRingHom
ValuationSubring.extendedIntegralModel
ValuationSubring.map_extendedIntegralModel_eq
ValuationSubring.pointSpecialization
ValuationSubring.pointSpecialization_inertia
FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero
WeierstrassCurve.torsion_fixed_of_invariant_injective

-- NEW 1: checked proof shape
theorem ValuationSubring.natCast_isUnit_of_residue_ne_zero
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)] :
    IsUnit (n : A)

-- NEW 2: checked proof shape
theorem ValuationSubring.torsionAffineX_mem
    {x y : ksep}
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular x y)
    (htor :
      (n : ℤ) •
        (WeierstrassCurve.Affine.Point.some x y hxy :
          (E.map (algebraMap k ksep)).toAffine.Point) = 0) :
    x ∈ A

-- NEW 3: checked proof shape; torsion-independent once x is integral
theorem ValuationSubring.affineY_mem_of_x_mem
    {x y : ksep}
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    y ∈ A

-- NEW 4: normalization/projective assembly
theorem ValuationSubring.pointSpecialization_some_ne_zero_of_mem
    {x y : ksep}
    (hxy : (E.map (algebraMap k ksep)).toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A) :
    A.pointSpecialization R k E hA
      (WeierstrassCurve.Affine.Point.some x y hxy) ≠ 0

-- NEW 5: zero-fibre theorem on torsion
theorem ValuationSubring.pointSpecialization_eq_zero_iff_on_torsion
    (P : (E⁄ksep).Point)
    (hP : P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)) :
    A.pointSpecialization R k E hA P = 0 ↔ P = 0

-- NEW 6: exact remaining geometric bridge
theorem ValuationSubring.pointSpecialization_sub_eq_zero_of_eq
    (P Q : (E⁄ksep).Point)
    (hPQ :
      A.pointSpecialization R k E hA P =
      A.pointSpecialization R k E hA Q) :
    A.pointSpecialization R k E hA (P - Q) = 0

-- NEW 7: assembly
theorem ValuationSubring.pointSpecialization_injective_on_torsion :
    Set.InjOn (A.pointSpecialization R k E hA)
      ((AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ) :
          AddSubgroup (E⁄ksep).Point) :
        Set (E⁄ksep).Point)
```

`NEW 6` may instead be supplied by `pointSpecialization_zero` plus `pointSpecialization_add` and an `AddMonoidHom`; that is a stronger, more reusable interface but not the smallest closure boundary.

## 5. Smallest honest kernel-green tranche

Proposed tranche: `NEW 1` through `NEW 5` only.

It would establish:

> Every nonzero `n`-torsion point has integral affine coordinates and therefore does not lie in the zero fibre of `pointSpecialization`.

This advances the target without assuming additivity, injectivity, formal-group correspondence, or the target theorem.

Required gates:

1. Direct build of the new narrow module.
2. Rebuild `GoodReduction.lean`.
3. `#print axioms` on all five declarations; each must exclude `sorryAx` and custom axioms.
4. Raw prohibited-token scan of the new source and the exact dictionary import chain.
5. Negative controls for missing `NeZero`, residue characteristic two with even `n`, integral affine `Z=1` versus infinity, and arbitrary noncomplete `A`.
6. Conditional assembly probe from `NEW 6` and `NEW 5` to `NEW 7`, then through the already reviewed Stage 6 prefix.
7. Only after that, umbrella builds and independent review.

Stop-loss conditions:

- Stop if any proof introduces `CompleteSpace A`, `T2Space A`, `IsAdic`, Henselianity, residue-characteristic exclusions, or oddness into the generic theorem.
- Stop if `NEW 4` requires changing the reviewed specialization definition rather than proving a normalization lemma.
- Stop if `NEW 6` cannot be isolated from torsion and begins reproducing the target theorem.
- Do not replace `NEW 6` by an assumed `AddMonoidHom`, assumed injectivity, or a structure whose field is the desired kernel theorem.

## 6. Exact residual after the tranche

After `NEW 1`–`NEW 5`, the sole target-local mathematical claim is:

```lean
∀ P Q : (E⁄ksep).Point,
  A.pointSpecialization R k E hA P =
      A.pointSpecialization R k E hA Q →
  A.pointSpecialization R k E hA (P - Q) = 0
```

Equivalently, prove that `pointSpecialization` is an additive homomorphism. Once that is kernel-clean, the torsion injectivity leaf and the unchanged `torsion_unramified_of_good_reduction` are short assemblies through existing reviewed declarations.

The remaining literature item is the actual proof text—or another primary, equivalently precise source—for AEC VII.2.2 and VII.3.1(a)/(b), especially the local-parameter/group-law correspondence over the intended valuation-ring scope. The available Advanced Topics volume confirms the result and citations but does not fill that source gap.

