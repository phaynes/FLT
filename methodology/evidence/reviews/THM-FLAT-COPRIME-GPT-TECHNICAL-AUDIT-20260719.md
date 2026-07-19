# THM-FLAT-COPRIME GPT-5.6 technical audit

## Decision

**Technical audit: PASS.** At the reviewed commit, Lean builds the target and reports that
`WeierstrassCurve.isCoprime_Φ_ΨSq` depends only on
`[propext, Classical.choice, Quot.sound]`; it does not depend on `sorryAx` or on the separately
admitted theorem `WeierstrassCurve.resultant_Φ_ΨSq`.

This is **not final independent approval**. The Helios theorem contract remains
`proof_status: kernel-clean`, `review_status: review-pending`. Fable must perform the independent
approval gate before `THM-FLAT-COPRIME` can be counted as reviewed or closed.

## Scope and provenance

- Helios task: `task:ca-flt-thm-flat-coprime-review-20260719`
- Technical auditor: GPT-5.6, xhigh
- Audit completed: `2026-07-19T12:47:04Z`
- Worktree: `/Volumes/second-store/devel/proof-forks/FLT-flat-coprime-review-20260719`
- Branch: `codex/ca-flt-thm-flat-coprime-review-20260719`
- Reviewed commit: `f49046d948046b487ae46f2cc55d70e7cb9bc4c5`
- Target contract: `THM-FLAT-COPRIME`
- Target declaration: `WeierstrassCurve.isCoprime_Φ_ΨSq`
- Excluded proof target: `THM-FLAT-RESULTANT` / `WeierstrassCurve.resultant_Φ_ΨSq`
- No proof source was changed during this audit.
- No theorem-contract status was promoted during this audit.

## Source and signature inspection

The reviewed source is `FLT/KnownIn1980s/EllipticCurves/Flat.lean`:

- Lines 245--251 contain `WeierstrassCurve.resultant_Φ_ΨSq`; line 251 remains `sorry`.
- Lines 260--262 contain the unchanged public signature of
  `WeierstrassCurve.isCoprime_Φ_ΨSq`:

  ```lean
  theorem WeierstrassCurve.isCoprime_Φ_ΨSq {R₀ : Type*} [CommRing R₀]
      (W : WeierstrassCurve R₀) {n : ℤ} (hn : n ≠ 0) (hΔ : IsUnit W.Δ) :
      IsCoprime (W.Φ n) (W.ΨSq n) := by
  ```

- Lines 263--309 contain the kernel-checked proof.
- Lines 287--288 use `W'.isCoprime_Φ_ΨSq_field hΔ' hn` after passage to the quotient field.
- Lines 301--309 map that coprimality statement to the alleged common root and derive the
  contradiction.
- No occurrence of `resultant_Φ_ΨSq` appears in the target proof body at lines 260--309.

The reviewed file is byte-identical to the file at the reviewed commit:

```text
$ git diff --exit-code f49046d948046b487ae46f2cc55d70e7cb9bc4c5 -- FLT/KnownIn1980s/EllipticCurves/Flat.lean
<no output; exit 0>

$ git show f49046d948046b487ae46f2cc55d70e7cb9bc4c5:FLT/KnownIn1980s/EllipticCurves/Flat.lean | shasum -a 256
463a2015547d47ba767c4eeb477d2a60852622b131f2157aa9d1e252925eeefa  -

$ shasum -a 256 FLT/KnownIn1980s/EllipticCurves/Flat.lean
463a2015547d47ba767c4eeb477d2a60852622b131f2157aa9d1e252925eeefa  FLT/KnownIn1980s/EllipticCurves/Flat.lean
```

The historical diff from `b004b473` to the reviewed commit changes the target body from `sorry`
to the quotient-field argument but does not alter its parameters or result type.

## Executable evidence

### Main target

Command:

```text
lake build FLT.KnownIn1980s.EllipticCurves.Flat
```

This fresh worktree initially populated `.lake/packages`, cloning pinned Mathlib revision
`a3364faec42918fcd84a03a255b50570129f9ead`, and then compiled the complete dependency closure.
Terminal output:

```text
✔ [2562/2563] Built Mathlib.AlgebraicGeometry.EllipticCurve.Reduction (7.9s)
✔ [2563/2563] Built FLT.KnownIn1980s.EllipticCurves.Flat (3.0s)
Build completed successfully (2563 jobs).
```

Result: PASS.

### Target-specific axiom audit

Command:

```text
lake build FLTMethodology.Probes.DivisionPolynomialCoprimeAudit
```

Exact output:

```text
ℹ [2557/2557] Built FLTMethodology.Probes.DivisionPolynomialCoprimeAudit (1.9s)
info: FLTMethodology/Probes/DivisionPolynomialCoprimeAudit.lean:15:0: 'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (2557 jobs).
```

Result: PASS. `sorryAx` is absent.

### Boundary and independence audit

Command:

```text
lake build FLTMethodology.Probes.FlatResultantAudit
```

Exact output:

```text
ℹ [2557/2557] Built FLTMethodology.Probes.FlatResultantAudit (3.0s)
info: FLTMethodology/Probes/FlatResultantAudit.lean:17:0: 'WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/FlatResultantAudit.lean:18:0: 'WeierstrassCurve.resultant_Φ_ΨSq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/FlatResultantAudit.lean:19:0: 'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (2557 jobs).
```

Result: PASS for the scoped target. This makes the boundary explicit: the universal resultant
remains admitted, but the coprime theorem's axiom closure does not include that admission.

## Findings

1. The target declaration builds at the exact reviewed commit.
2. The target has no `sorryAx` dependency.
3. The adjacent universal resultant still has `sorryAx` and remains a separate open theorem.
4. The target proof invokes the field-level coprimality provider, not the admitted resultant.
5. The public target signature is unchanged; only the former admitted body was replaced.
6. `FLTMethodology/Probes/DivisionPolynomialCoprimeAudit.lean` lines 11--12 contain a stale
   comment claiming a dependency on the admitted resultant. Its executable `#print axioms`
   output disproves that comment. Correcting the comment should be a separate documentation task;
   it does not affect kernel evidence.

## Residual integration and approval gaps

- Fable independent approval is required before changing `THM-FLAT-COPRIME.review_status` from
  `review-pending` to `reviewed` or counting this theorem as independently closed.
- Consumer integration remains open. `WeierstrassCurve.torsion_flat_of_good_reduction` is still
  admitted and the programme contract records dependencies on both `THM-FLAT-COPRIME` and the
  separately open `THM-FLAT-RESULTANT`.
- `THM-FLAT-RESULTANT` remains admitted and outside this audit's closure claim.
- The stale prose in `DivisionPolynomialCoprimeAudit.lean` should be corrected under a separate
  task so the human-readable audit description matches the executable result.

## Technical-audit conclusion

GPT-5.6 technical audit **PASS** for build integrity, axiom closure, signature preservation, and
independence from `THM-FLAT-RESULTANT`. Final independent theorem review is **not closed**; Fable
approval remains required.
