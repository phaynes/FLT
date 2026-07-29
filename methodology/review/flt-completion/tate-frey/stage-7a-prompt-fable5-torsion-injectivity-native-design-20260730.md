# Stage 7A — Fable 5 native torsion-injectivity design

Work read-only in the supplied isolated FLT worktree. Do not edit files, build a replacement theorem
with assumptions, mutate Helios, or claim proof progress.

## Frozen boundary

- repository: `/Volumes/second-store/devel/proof-forks/FLT-good-reduction-specialization-20260730`
- branch: `codex/ca-flt-good-reduction-specialization-20260730`
- reviewed baseline: `15dba9d`
- task: `task:ca-flt-good-reduction-specialization-20260730`
- obligation: `FLT-TATE-UNRAMIFIED`
- target: `WeierstrassCurve.torsion_unramified_of_good_reduction`

Stage 6 independently passed the point-specialization and inertia-invariance prefix. The exact open
leaf is:

```lean
Set.InjOn (A.pointSpecialization R k E hA)
  (AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))
```

under `NeZero (n : IsLocalRing.ResidueField R)`.

## Experimental control

Develop the strongest design available from the actual Lean repository, pinned Mathlib, and your
own mathematical reasoning. Do **not** read the external FLT literature corpus or literature-derived
design notes. You may read source comments inside the code because they are part of the implementation
being audited. This is the no-literature arm and must remain distinguishable from Stage 7B.

## Corrections that must be respected

1. The exact torsion dictionary already exists and is kernel-clean:
   `FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero` in
   `FLT/EllipticCurve/TorsionProof/PsiSqExactDetection.lean`. Audit its import graph before proposing
   reuse; do not repeat the earlier false claim that this dictionary is absent.
2. `ΨSq` is a squared division polynomial. A generic appeal to the discriminant or separability of
   `ΨSq` is invalid. Check the definitions of `preΨ`, `Ψ`, and `ΨSq` before proposing a
   squarefree-root argument.
3. `isCoprime_Φ_ΨSq` is proved, but coprimality alone does not prove reduction injective on
   the full projective torsion set.
4. The vendored formal-group files include explicit `sorry` boundaries and at least one documented
   simplification in negative multiplication coefficients. No design may inherit an admission or a
   mathematically inaccurate definition.
5. A total invariant specialization function is already proved. Do not rebuild it unless you exhibit
   a concrete defect in the reviewed prefix.

## Required analysis

Inspect exact declarations and compare, at minimum:

- a kernel-of-reduction/formal-parameter proof of no prime-to-residue-characteristic torsion;
- a proof that specialization is an additive homomorphism followed by a kernel argument;
- a full division-polynomial or finite-etale-coordinate argument, including the sign/y-coordinate
  problem and even torsion;
- any smaller route already latent in pinned Mathlib or the axiom-clean part of the vendored library.

For each route, name the first missing mathematical lemma, the exact Lean types it would use, import
cycles, existing admissions in its closure, and an executable falsification probe. Explicitly test
characteristics two and three, arbitrary valuation subrings of the separable closure, noncomplete
valuation rings, even `n`, and the point at infinity.

If the generic target is substantially broader than the actual odd-prime FLT consumer, quantify the
difference and give exact consumer evidence. You may propose a consumer-specialized theorem as a
separate route, but may not present it as closure of the unchanged generic target.

## Output contract

Return:

1. one leading verdict: `IMPLEMENTABLE`, `IMPLEMENTABLE-AFTER-NAMED-LEAVES`, or
   `STATEMENT-OR-LIBRARY-BLOCKED`;
2. a ranked route comparison with rejection reasons;
3. exact proposed Lean signatures in dependency order, marking every existing declaration and every
   new declaration;
4. the smallest honest kernel-green build tranche that advances the target without adding an
   assumption or a target-equivalent contract;
5. required direct builds, axiom audits, negative controls, and stop-loss condition;
6. the exact claim that would remain open after that tranche.

No prose citation, model confidence, successful elaboration of a contract, or existing `sorry` may
be treated as proof evidence.
