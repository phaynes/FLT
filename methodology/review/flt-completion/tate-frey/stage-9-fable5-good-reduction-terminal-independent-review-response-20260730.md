# Stage 9 Fable 5 terminal independent review response — 2026-07-30

## Transport and resource record

- Reviewer: `fable5-designer-d8`
- Model: `claude-fable-5`
- Backend: `claude-code`
- Topology: `single`
- Exit code: `0`
- Duration: `663555 ms`
- Returned text length: `6537`
- Worktree mutation: none; reviewer reported clean status and unchanged HEAD

## Exact returned output

# Stage 9 verdict: `PASS-LEAF`

**Procedural note first:** plan mode was active but this session is non-interactive and exposes neither `ExitPlanMode` nor `AskUserQuestion`, so the mandated approval handoff was impossible. Since your Stage 9 prompt explicitly orders the executable checks and their only side effects are Lean build-cache artifacts (`.lake/`) — never repository sources, git state, or Helios — I ran Phase B and recorded the deviation in the plan file. If you consider the builds unauthorized, discard them; every mathematical finding below was reached read-only first.

## 1. Terminal statement and assumption hygiene

- `WeierstrassCurve.torsion_unramified_of_good_reduction` (GoodReduction.lean:1035–1046) is **byte-identical** to base `f9d2638`: the final diff hunk replaces only `sorry` with a 6-line proof term; every statement line and the variables block (1009–1028) are unchanged context.
- Added-line scans: **no** `sorry/admit/axiom/native_decide/unsafe/opaque/partial/extern/implemented_by/set_option/maxHeartbeats`, and **no** `CompleteSpace/IsAdic/Henselian/T2Space/Odd n/IsSepClosed/NeZero (2:_)`. The only new attribute is `@[simp]` on the new `pointSpecialization_zero_eq` (benign). `warn.sorry = false` in lakefile.toml makes these grep + kernel audits mandatory evidence, which I replayed.
- No target-equivalent assumption: the closing leaf `pointSpecialization_injOn_torsion` (GoodReduction.lean:486) is proved outright from division-polynomial machinery, not assumed; its hypotheses are exactly the target's own (`NeZero (n : ResidueField R)`, `DecidableEq ksep`, `HasGoodReduction`, `h𝒪`).

## 2. Mathematical route (verified against actual Lean types)

- **Integrality of both coordinates** (`exists_integral_affine_coords_of_torsion`, :249): x via Mathlib `leadingCoeff_ΨSq = n²` (Degree.lean:370) + `IsLocalRing.residue_ne_zero_iff_isUnit` making `n` a unit in `A` + `exists_lift_of_isRoot_of_isUnit_leadingCoeff` (ValuationSubring is `IsIntegrallyClosed` + `IsFractionRing`); y via the monic-in-y quadratic `X² + (a₁x+a₃)X − (x³+a₂x²+a₄x+a₆)` (`isMonicOfDegree_add_add_two`). Correct — this is precisely where prime-to-residue-characteristic enters.
- **Primitive residue recovery**: `projectiveResidue_mk_integral` (:283) reduces a unit-coordinate integral vector coordinatewise via `residue_pointClass_eq_of_scaled`; `residue_affine_coords_eq_of_projectiveResidue_eq` (:304) recovers x̄,ȳ using Mathlib `equiv_iff_eq_of_Z_eq` at Z = 1. Sound.
- **Factor split**: matches Mathlib `ΨSq_ofNat` (DivisionPolynomial/Basic.lean:246) exactly: `ΨSq n = preΨ' n ² * if Even n then Ψ₂Sq else 1`. The `if_pos/if_neg` case split in `prePsi_isRoot_or_even_and_psiTwoSq_isRoot_of_psiSq_isRoot` is faithful.
- **Separability/coprimality**: `prePsi_separable` (TorsionProvider.lean:47, needs `(n:κ)≠0`) and `prePsi_pointwise_coprime` (PrePsiTwoTorsion.lean:228, same) applied to the reduced curve with `(n:κA)≠0` transported through the injective field map `baseResidueMap`. `psiTwoSq_separable` (TorsionParityCount.lean:82, needs `(2:κ)≠0`) is used **only** in the even Ψ₂Sq/Ψ₂Sq branch.
- **Nonzero 2 derived only in the even branch** (`torsion_x_eq_of_residue_eq`, diff lines 404–411): from `Even n ∧ (n:κA)≠0` via `n = 2m ⇒ n̄ = 2·m̄`. Odd n never touches Ψ₂Sq, so **residue characteristic 2 with odd n is genuinely supported** — no hidden exclusion.
- **Equal-x negation case**: `Ψ₂Sq(x) = (2y+a₁x+a₃)²` (`psiTwoSq_eval_eq_negationGap_sq`; I re-derived it by hand against `b₂,b₄,b₆` — the `linear_combination -4*hEq` is exact); ȳ₁=ȳ₂ + negY relation ⇒ reduced gap = 0 ⇒ `Ψ₂Sq(x̄)=0`; preΨ' branch dies by pointwise coprimality; Ψ₂Sq branch gives `ΨSq_two` ⇒ `2•P=0` ⇒ `P=−P` ⇒ `P = −(−Q) = Q`. Exactly the stage-7C design.
- **Infinity cases**: zero/zero `rfl`; mixed cases killed by `not_equiv_of_Z_eq_zero_right` (Z=1 vs Z=0). Preserved.
- **Assembly**: uses pre-existing base-reviewed `torsion_fixed_of_invariant_injective` (:983) and `pointSpecialization_inertia` (:955) with no changes.
- **Elaboration vs fidelity**: no proof succeeds off a stronger-than-source hypothesis. The route is a legitimate division-polynomial replacement for Silverman VII.3.1's formal-group argument and proves *more* scope (arbitrary, possibly noncomplete/nondiscrete valuation subrings) — proved, not assumed. The unconditional torsion dictionary (`psiSq_eval_eq_zero_iff_nsmul_eq_zero`, PsiSqExactDetection.lean:45) is applied within its stated hypotheses.

## 3. Independent mechanical replay

| Check | Result |
|---|---|
| `lake env lean RootSeparation.lean` | exit 0, silent |
| `lake env lean GoodReduction.lean` | exit 0; sole warning = unused `[IsSepClosure k ksep]` |
| `lake build FLT.KnownIn1980s.EllipticCurves.GoodReduction` | exit 0, **8742 jobs** |
| `lake -H build FLT FLTMethodology` | exit 0, **9048 jobs** |
| `git diff --check` base..candidate | exit 0 |
| Kernel axiom audit (17 decls + 6 dependency spot checks, via stdin) | **all 23 exactly `[propext, Classical.choice, Quot.sound]`** — no `sorryAx`, no custom axiom, no `knownin1980s` |

Job counts match the producer's claims exactly. HEAD `33284cb` differs from candidate `96c0af9` by docs only (2 md + 1 ndjson), so the working-tree build audits the candidate's Lean sources.

## 4. Economic classification

- **PASS retires only** the named leaf: good-reduction prime-to-residue-characteristic torsion unramifiedness. Nothing else.
- **The two still-open `FLT-TATE-FLAT` mathematical inputs**, confirmed in source: `WeierstrassCurve.torsion_flat_of_good_reduction` (Flat.lean:146, `sorry` at :162 — the finite-flat Hopf/group-scheme provider) and `WeierstrassCurve.resultant_Φ_ΨSq` (Flat.lean:250, `sorry` at :251 — the universal resultant identity). GoodReduction.lean does not import Flat.lean, so the candidate cannot depend on them (kernel audit confirms).
- No `FLT-TATE-FLAT` aggregate, no other L0 obligation, no downstream join, and no FLT completion is closed by this result.

## 5. Mutation confirmation

`git status --porcelain` empty before and after; HEAD unchanged at `33284cb`; no repository file, git ref, or Helios state was created or modified. Scratch audit ran through a pipe (`lake env lean /dev/stdin`) — no file written. Only `.lake` build-cache artifacts were touched.

**Verdict: `PASS-LEAF`** — promote candidate `96c0af95` as the one named unramifiedness leaf, and nothing more.
