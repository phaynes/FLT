# Stage 7B — GPT-5.6 xhigh literature-anchored torsion-injectivity design

Work read-only in the supplied isolated FLT worktree. Do not edit files, mutate Helios, introduce an
assumption, or claim proof progress.

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

## Literature arm

Use both the actual code and the available literature evidence. Read the relevant portions of:

- `/Volumes/second-store/devel/knowledge-base-mcp/mentormind-flt-three-project-completion-20260719/build/flt-literature-assurance/quarto/papers/SRC-024-silverman-advanced-topics-1994.qmd`, especially its references to AEC VII.3.1(b), AEC VII.2.2, the formal-group identification of the kernel of specialization, and the statement that the kernel has no prime-to-residue-characteristic torsion;
- `FLT/KnownIn1980s/EllipticCurves/Flat.lean` and its source comments;
- the local source/design and dependency-slice material for `FLT-TATE-UNRAMIFIED`.

The available Silverman volume cites the precise first-volume result but is not itself the complete
proof of AEC VII.3.1. Mark that source gap explicitly; do not invent text or theorem numbers beyond
what the corpus establishes. Primary literature is preferred but not a prerequisite for a bounded
kernel-green tranche.

## Corrections that must be respected

1. The exact kernel-clean torsion dictionary already exists:
   `FLTMethodology.Torsion.psiSq_eval_eq_zero_iff_nsmul_eq_zero` in
   `FLT/EllipticCurve/TorsionProof/PsiSqExactDetection.lean`. Check its import graph.
2. `ΨSq` is a squared division polynomial. Its ordinary discriminant cannot provide the missing
   distinct-root theorem. Audit `preΨ`, `Ψ`, and `ΨSq` and correct any misleading source comment.
3. `isCoprime_Φ_ΨSq` does not by itself establish full point-level injectivity, including the
   sign/y-coordinate and even-torsion cases.
4. The vendored formal-group work contains admissions and documented simplifications; segregate
   axiom-clean reusable algebra from unproved or inaccurate curve-correspondence claims.
5. Do not rebuild the independently reviewed specialization/inertia prefix without a demonstrated
   defect.

## Required design analysis

Reconstruct the mathematical proof anatomy of the standard formal-group route:

```text
kernel of reduction at O
  ↔ positive valuation of the local parameter
  → [n](T) = nT + higher terms
  → n a unit preserves the leading valuation
  → no nonzero n-torsion in the kernel
  → reduction injective on n-torsion.
```

Then map every arrow to actual Lean types and available declarations. Determine whether the proof
can be made algebraic over an arbitrary valuation subring (without a completeness assumption), or
whether a completion/topological evaluation route would silently weaken the theorem. Compare this
against:

- proving additivity of `pointSpecialization` and then a kernel theorem;
- a finite-etale/full coordinate-ring route;
- a corrected division-polynomial route based on a squarefree factor rather than `ΨSq`;
- a consumer-specialized odd-prime theorem if and only if exact FLT consumer evidence shows it is a
  materially smaller, useful boundary. Keep it distinct from closure of the generic target.

For every route, identify the first missing mathematical lemma, exact signature, import graph,
admission closure, source support, and a fast executable falsification probe. Test arbitrary
valuation subrings of the separable closure, noncomplete rings, even `n`, the point at infinity,
and characteristics two and three.

## Output contract

Return:

1. one leading verdict: `IMPLEMENTABLE`, `IMPLEMENTABLE-AFTER-NAMED-LEAVES`, or
   `STATEMENT-OR-LIBRARY-BLOCKED`;
2. a source-to-Lean proof map separating sourced mathematics from implementation inference;
3. a ranked route comparison with rejection reasons;
4. exact proposed Lean signatures in dependency order, marking existing versus new declarations;
5. the smallest honest kernel-green build tranche, with direct build, axiom-audit, negative-control,
   and stop-loss gates;
6. the exact remaining claim after that tranche and any literature item still missing.

No prose citation, model confidence, contract elaboration, or theorem with `sorryAx` is proof
evidence.
