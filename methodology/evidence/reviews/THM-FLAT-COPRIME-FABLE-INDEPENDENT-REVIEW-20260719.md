# THM-FLAT-COPRIME Fable independent review

## Decision

**Independent review: PASS.** At the reviewed commit, the target declaration
`WeierstrassCurve.isCoprime_Φ_ΨSq` builds, its kernel-reported axiom closure is
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`), it neither references nor
inherits the separately admitted `WeierstrassCurve.resultant_Φ_ΨSq`, and its public
signature is unchanged from the pre-proof baseline. `review_status` for
`THM-FLAT-COPRIME` is promoted to `reviewed`; `proof_status` remains `kernel-clean`.
Consumer integration remains the residual gap (see below).

## Scope and provenance

- Reviewer: Claude Fable 5 (model id `claude-fable-5`), acting as the independent
  approval gate. This review was performed independently of, and after, the GPT-5.6
  technical audit at
  `methodology/evidence/reviews/THM-FLAT-COPRIME-GPT-TECHNICAL-AUDIT-20260719.md`,
  which was treated as evidence to check, not as authority.
- Review completed: `2026-07-19T12:51:53Z`
- Worktree: `/Volumes/second-store/devel/proof-forks/FLT-flat-coprime-review-20260719`
- Branch: `codex/ca-flt-thm-flat-coprime-review-20260719`
- Reviewed commit: `f49046d948046b487ae46f2cc55d70e7cb9bc4c5` (= `HEAD` at review time)
- Toolchain: `leanprover/lean4:v4.32.0-rc1`; pinned Mathlib revision
  `a3364faec42918fcd84a03a255b50570129f9ead` (verified in `lake-manifest.json`)
- Target contract: `THM-FLAT-COPRIME`, declaration `WeierstrassCurve.isCoprime_Φ_ΨSq`
- Explicitly excluded from the closure claim: `THM-FLAT-RESULTANT`, declaration
  `WeierstrassCurve.resultant_Φ_ΨSq` (still admitted; reported separately below)
- No proof source was changed during this review. Files written by this review:
  this document and the `THM-FLAT-COPRIME` line of
  `methodology/control/theorem-contracts.ndjson`.

## Source inspection (`FLT/KnownIn1980s/EllipticCurves/Flat.lean`)

Verified by direct reading at the reviewed commit:

- Lines 245–251: `WeierstrassCurve.resultant_Φ_ΨSq` (universal resultant identity);
  line 251 is `sorry`. This is the admitted declaration, reported separately below.
- Lines 260–262: public signature of the target, verbatim:

  ```lean
  theorem WeierstrassCurve.isCoprime_Φ_ΨSq {R₀ : Type*} [CommRing R₀] (W : WeierstrassCurve R₀)
      {n : ℤ} (hn : n ≠ 0) (hΔ : IsUnit W.Δ) :
      IsCoprime (W.Φ n) (W.ΨSq n) := by
  ```

  The declaration sits under `@[expose] public section` (line 114), so it is public.
- Lines 263–309: the proof body. Structure: reduce coprimality to
  `1 ∈ Ideal.span {Φ n, ΨSq n}`; assume not, embed the span in a maximal ideal `M`
  (lines 273–275); pass to the quotient field `S = R₀[X]/M` (lines 276–282); the
  discriminant stays nonzero because `IsUnit W.Δ` maps to a unit (lines 283–286);
  invoke the field-level provider `W'.isCoprime_Φ_ΨSq_field hΔ' hn` (lines 287–288);
  evaluate at the image of `X`, where both polynomials vanish since they lie in `M`
  (lines 289–308); conclude via `not_isCoprime_zero_zero` (line 309).
- Independence, textual: the identifier `resultant_Φ_ΨSq` has zero occurrences in
  lines 260–309 (checked with `grep`/`sed` over that exact range). The docstring at
  lines 253–259 mentions the resultant only to state the proof does *not* use it.
- Independence, kernel-level: the axiom audit below shows no `sorryAx` in the
  target's closure. Any dependence, direct or transitive, on the admitted resultant
  would necessarily surface as `sorryAx` there; this is stronger than the textual check.

File integrity against the reviewed commit:

```text
$ git diff --exit-code f49046d948046b487ae46f2cc55d70e7cb9bc4c5 -- FLT/KnownIn1980s/EllipticCurves/Flat.lean
<no output; exit 0>

$ shasum -a 256 FLT/KnownIn1980s/EllipticCurves/Flat.lean
463a2015547d47ba767c4eeb477d2a60852622b131f2157aa9d1e252925eeefa  FLT/KnownIn1980s/EllipticCurves/Flat.lean

$ git show f49046d948046b487ae46f2cc55d70e7cb9bc4c5:FLT/KnownIn1980s/EllipticCurves/Flat.lean | shasum -a 256
463a2015547d47ba767c4eeb477d2a60852622b131f2157aa9d1e252925eeefa  -
```

Signature stability: at pre-proof commit `b004b473` the same declaration (then at
lines 238–241, body `sorry`) has byte-identical binders and result type
(`{R₀ : Type*} [CommRing R₀] (W : WeierstrassCurve R₀) {n : ℤ} (hn : n ≠ 0)
(hΔ : IsUnit W.Δ) : IsCoprime (W.Φ n) (W.ΨSq n)`). Only the body changed.

## Executable evidence (rerun by this reviewer)

### 1. Main target build

```text
$ lake build FLT.KnownIn1980s.EllipticCurves.Flat
Build completed successfully (2556 jobs).
```

Result: PASS. (This worktree was already populated by the earlier audit, so the build
is incremental; the job count differs from the GPT audit's fresh-clone count of 2563
for that benign reason.)

### 2. Target axiom audit

```text
$ lake build FLTMethodology.Probes.DivisionPolynomialCoprimeAudit
ℹ [2557/2557] Replayed FLTMethodology.Probes.DivisionPolynomialCoprimeAudit
info: FLTMethodology/Probes/DivisionPolynomialCoprimeAudit.lean:15:0: 'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (2557 jobs).
```

Result: PASS. No `sorryAx`.

### 3. Boundary and independence audit

```text
$ lake build FLTMethodology.Probes.FlatResultantAudit
ℹ [2557/2557] Replayed FLTMethodology.Probes.FlatResultantAudit
info: FLTMethodology/Probes/FlatResultantAudit.lean:17:0: 'WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/FlatResultantAudit.lean:18:0: 'WeierstrassCurve.resultant_Φ_ΨSq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/FlatResultantAudit.lean:19:0: 'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (2557 jobs).
```

Result: PASS for the target; the admitted resultant's `sorryAx` is visible and
confined to `resultant_Φ_ΨSq`.

### 4. Fresh kernel re-check (cache-independent)

Because lake replayed the probe logs from its content-addressed cache (a `touch` does
not force re-elaboration), this reviewer additionally ran the `#print axioms` commands
in a scratch file outside the build cache, forcing fresh elaboration through the
kernel:

```text
$ lake env lean /tmp/fable-flat-coprime-axiom-check.lean
'WeierstrassCurve.isCoprime_Φ_ΨSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.resultant_Φ_ΨSq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.resultant_Φ_ΨSq_explicit_eq_default' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(Scratch file contents: `module` / `public import FLT.KnownIn1980s.EllipticCurves.Flat`
followed by the three `#print axioms` commands.) The freshly elaborated results agree
exactly with the replayed probe outputs.

## Admitted resultant — reported separately and explicitly

`WeierstrassCurve.resultant_Φ_ΨSq` (`FLT/KnownIn1980s/EllipticCurves/Flat.lean:245`–`251`)
**remains admitted**: its body is `sorry` (line 251) and its axiom closure contains
`sorryAx`. It is the `THM-FLAT-RESULTANT` contract, is *not* covered by this approval,
and nothing in this review promotes it. The kernel evidence above shows the approved
coprime theorem does not depend on it. The adjacent normalisation lemma
`resultant_Φ_ΨSq_explicit_eq_default` (lines 225–239) is kernel-clean.

## Assessment of the GPT-5.6 technical audit

Checked claim by claim against this reviewer's independent reruns:

- Reviewed commit, branch, worktree, and Mathlib pin: accurate.
- File sha256 (`463a2015…eefa`) and clean `git diff` against the commit: reproduced.
- Source line references (245–251, 251 `sorry`, 260–262 signature, 263–309 body,
  287–288 field provider, 301–309 contradiction): all accurate.
- Probe outputs: the `info:` lines reported by the audit are byte-identical to those
  reproduced here, and to the fresh cache-independent kernel check.
- Main-build job count: the audit reports 2563 jobs (fresh clone including Mathlib
  compilation); this rerun saw 2556 (warm cache). Benign, explained, not a discrepancy
  in evidence.
- The audit's finding of stale prose in the coprime probe is correct and is confirmed
  below.

Conclusion: the GPT audit accurately reports its commands and results.

## Noted without expanding scope

`FLTMethodology/Probes/DivisionPolynomialCoprimeAudit.lean` lines 11–12 state the
probe "makes its remaining dependency on the admitted division-polynomial resultant
identity visible". That prose is stale: the executable `#print axioms` output in the
same file disproves any such remaining dependency. This is documentation drift only;
correcting it belongs to a separate documentation task and does not affect the kernel
evidence or this approval.

## Residual gap: consumer integration

The consumer `WeierstrassCurve.torsion_flat_of_good_reduction`
(`FLT/KnownIn1980s/EllipticCurves/Flat.lean:146`–`162`) is still admitted (`sorry`,
line 162), and its contract `THM-FLAT-GOOD-REDUCTION` records dependencies on both
`THM-FLAT-COPRIME` and the still-open `THM-FLAT-RESULTANT`. Approving
`THM-FLAT-COPRIME` closes the coprimality provider only; wiring it into the finite-flat
consumer (and settling `THM-FLAT-RESULTANT`) remains open and is retained as the
residual gap on the contract record.

## Ledger action taken

Per the approval-gate instructions, exactly one record in
`methodology/control/theorem-contracts.ndjson` was updated — `THM-FLAT-COPRIME`:
`review_status` `review-pending` → `reviewed`; `proof_status` kept `kernel-clean`;
`residual_gap` updated to record consumer integration as the sole remaining gap.
No other record was touched. No proof source was edited; nothing was committed,
pushed, or approved in any task system.

## Conclusion

**PASS.** Reviewer model: Claude Fable 5 (`claude-fable-5`).
