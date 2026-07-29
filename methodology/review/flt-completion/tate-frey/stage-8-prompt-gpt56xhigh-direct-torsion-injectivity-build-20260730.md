# Stage 8 — GPT-5.6 xhigh direct torsion-injectivity build

You are the sole proof-mutating builder in the isolated worktree supplied as `--root`. Work under
the already executing Helios task `task:ca-flt-good-reduction-specialization-20260730`. Do not
create or transition tasks and do not perform git operations; the controller owns task and git
state. Preserve all existing work.

## Frozen boundary

- expected branch: `codex/ca-flt-good-reduction-specialization-20260730`
- expected starting HEAD: the controller commit containing Stage 7A, 7B, and 7C records
- target: `WeierstrassCurve.torsion_unramified_of_good_reduction`
- exact open leaf: injectivity of `ValuationSubring.pointSpecialization` on
  `AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)`
- original target statement must remain unchanged
- reviewed Stage 5/6 specialization and inertia prefix must not be replaced

## Evidence to read first

Read completely:

1. `methodology/review/flt-completion/tate-frey/stage-7a-fable5-torsion-injectivity-native-design-response-20260730.md`
2. `methodology/review/flt-completion/tate-frey/stage-7b-gpt56xhigh-torsion-injectivity-literature-design-response-20260730.md`
3. `methodology/review/flt-completion/tate-frey/stage-7c-root-torsion-injectivity-synthesis-and-probe-20260730.md`
4. `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`
5. `FLT/EllipticCurve/TorsionProof/PsiSqExactDetection.lean`
6. `FLT/EllipticCurve/TorsionProvider.lean`
7. `FLT/EllipticCurve/TorsionProof/PrePsiTwoTorsion.lean`

The controller's current scratch proof is available at
`/tmp/flt-root-separation.FVrOEB/Probe.lean`. Its generic and specialization-prefix declarations
elaborate and audit to exactly `[propext, Classical.choice, Quot.sound]`. Use it as checked proof
material, but do not import it and do not copy its module structure blindly: it imports
`GoodReduction.lean`, so production generic helpers must be placed in an acyclic module.

## Objective ordering

Optimize verified closure probability first. Attempt the full unchanged target through the direct
factor-by-factor root-separation route in Stage 7C. If the full assembly cannot be completed within
the bounded run, retain only independently meaningful kernel-green declarations and report the
exact first failing goal. Never introduce a target-equivalent contract, new assumption, axiom,
`sorry`, `admit`, `by_contra` placeholder, or opaque evidence structure.

## Required route

1. Prove/port the generic separable-root reduction lemma: distinct roots over a domain cannot have
   equal residue when the mapped polynomial is separable.
2. Prove/port the unit-leading-coefficient integral-root lemma.
3. Prove affine torsion coordinates integral using the exact `ΨSq` dictionary and
   `leadingCoeff_ΨSq = n^2`; use the monic Weierstrass equation for `y`.
4. Prove explicit coordinatewise specialization for primitive integral affine triples and for
   zero.
5. Split a `ΨSq` root with the actual `ΨSq_ofNat` definition into `preΨ' n` or `Ψ₂Sq`.
6. On the reduced curve use:
   - `FLT.EllipticCurve.TorsionProvider.prePsi_separable`;
   - `FLTMethodology.Torsion.psiTwoSq_separable` only in the even branch where nonzero `n` forces
     nonzero `2`;
   - `FLTMethodology.Torsion.prePsi_pointwise_coprime` for cross-factor collisions.
7. After equal `x`, use `eq_or_eq_neg_of_xRep_eq_xRep`. Resolve the negation case with
   `Ψ₂Sq(x) = (2y + a₁x + a₃)^2`: a `preΨ'` root contradicts pointwise coprimality; a `Ψ₂Sq` root
   is two-torsion and hence self-negative by the exact dictionary at `2`.
8. Use the resulting `InjOn` lemma with the already proved
   `torsion_fixed_of_invariant_injective` and `pointSpecialization_inertia` to close the original
   theorem.

Do not switch to a formal-series evaluation, completeness, Henselian, finite-etale scheme-model,
or assumed-additivity route unless the direct route is falsified by an exact Lean goal. Do not use
`isCoprime_Φ_ΨSq` as a substitute for injectivity. Do not claim `ΨSq` itself is separable.

## Required verification

- direct elaboration of every changed/new Lean file;
- `#print axioms` for every new terminal declaration and the unchanged target;
- target must exclude `sorryAx` and custom axioms and should have exactly the standard trio;
- added-line prohibited-token scan;
- `git diff --check`;
- narrow build for `GoodReduction`;
- `lake -H build FLT FLTMethodology` if the direct files pass;
- preserve characteristic-two odd `n`, characteristic three, even `n`, noncomplete `A`, and the
  point-at-infinity cases;
- do not report a build that was not actually run.

## Response contract

Return:

1. exact declarations added or changed;
2. exact target status (`CLOSED`, `PREFIX-ONLY`, or `BLOCKED-AT-NAMED-LEAN-GOAL`);
3. commands, exit codes, job counts, warnings, and axiom outputs;
4. files changed and line counts;
5. any remaining mathematical or elaboration boundary stated as an exact Lean type;
6. confirmation that no git or Helios mutation was performed.

