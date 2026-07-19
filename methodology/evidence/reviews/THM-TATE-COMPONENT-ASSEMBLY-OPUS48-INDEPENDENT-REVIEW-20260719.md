# THM-TATE-COMPONENT-ASSEMBLY — Independent approval-gate review

**Date:** 2026-07-19
**Review model:** `claude-opus-4-8` (fallback invoked after Fable became unavailable)
**Role:** Independent approval gate (not the technical auditor). The GPT-5.6 audit at
`methodology/evidence/reviews/THM-TATE-COMPONENT-ASSEMBLY-GPT-TECHNICAL-AUDIT-20260719.md`
was treated as evidence to check, not as authority.
**Target declaration:** `WeierstrassCurve.tateEquivOfComponents`
**Frozen reviewed commit:** `160050be4d7066affd510f8076ca38f1f6980cf7`
**Worktree:** `/Volumes/second-store/devel/proof-forks/FLT-tate-component-review-20260719`

## Verdict

**PASS** for the bounded theorem contract `WeierstrassCurve.tateEquivOfComponents`.

The target is a complete, kernel-clean algebraic assembly whose independently reproduced
axiom closure is exactly `[propext, Classical.choice, Quot.sound]` — it does **not** contain
`sorryAx`. This verdict closes **only** the bounded change-of-variables join. It does **not**
close either mathematical provider, the aggregate `WeierstrassCurve.tateEquiv`, or any
downstream Tate uniformization consumer; those remain transitively admitted via `sorryAx`.

**Contract-registry update: NOT PERFORMED — target file absent (see §9).** The mandated file
`methodology/control/theorem-contracts.ndjson` does not exist in this worktree, in the frozen
commit tree, or anywhere reachable under the review directory, and no
`THM-TATE-COMPONENT-ASSEMBLY` record exists to update. The registry mutation was therefore
withheld rather than fabricated. This does not change the technical PASS on the bounded target;
it flags a governance gap for the operator to resolve.

---

## 1. Frozen review identity

```text
$ git rev-parse HEAD
160050be4d7066affd510f8076ca38f1f6980cf7
$ git branch --show-current
codex/ca-flt-thm-tate-component-assembly-review-20260719
$ git status --short
?? methodology/evidence/reviews/
```

Relevant commits (independently resolved):

- reviewed handoff commit: `160050be4d7066affd510f8076ca38f1f6980cf7`
- proof-introduction commit: `439c6b022046736319ec88f4c457f696cb9fbf02`
- pre-proof parent baseline: `git rev-parse 439c6b0^ = 1f6d11caee718028bf783c968511d34865ffd9f0`

HEAD is exactly the frozen commit. The only working-tree change is the untracked
`methodology/evidence/reviews/` directory (the GPT audit and this report). No tracked file is
modified (`git diff --stat` is empty). `.lake` build artifacts are gitignored and were not
committed.

## 2. Toolchain and dependency pin

```text
$ cat lean-toolchain           → leanprover/lean4:v4.32.0-rc1
$ lake --version               → Lake version 5.0.0-src+b4812ae (Lean version 4.32.0-rc1)
$ lean --version               → Lean (version 4.32.0-rc1, arm64-apple-darwin24.6.0,
                                       commit b4812ae53eea93439ad5dce5a5c26591c31cb697, Release)
$ lakefile.toml [[require]] mathlib rev = a3364faec42918fcd84a03a255b50570129f9ead
$ lake-manifest.json mathlib inputRev = a3364faec42918fcd84a03a255b50570129f9ead
```

All match the pins cited by the GPT audit. Mathlib artifacts were present and cached (8270
`.olean` files under `.lake/packages/mathlib`); no network fetch was required.

## 3. Byte-identity of reviewed source to the frozen commit

Working-tree blob hashes equal the frozen-commit blob hashes for all three reviewed files:

| File | Working tree `git hash-object` | Frozen `160050be:<path>` |
|---|---|---|
| `FLT/KnownIn1980s/EllipticCurves/TateCurve.lean` | `98551af43a86b7580dde6366f1e885de4861521a` | `98551af…` (identical) |
| `FLTMethodology/Probes/TateUniformizationAssembly.lean` | `61325b223e532cee46d34a987083bf762d0f26d2` | `61325b2…` (identical) |
| `methodology/review/flt-completion/tate-frey/implementation-handoff-20260719.md` | `3dc289abefa7fb3ff7ea8aad2601382f91b673f7` | `3dc289a…` (identical) |

These three hashes also match the values recorded in the GPT audit §1. The reviewed source is
byte-identical to the frozen commit.

## 4. Signature and history audit

**Post-introduction stability.** The two proof-carrying files are unchanged between the
introduction commit and the frozen commit:

```text
$ git diff --stat 439c6b0..HEAD -- \
    FLT/KnownIn1980s/EllipticCurves/TateCurve.lean \
    FLTMethodology/Probes/TateUniformizationAssembly.lean
(empty; exit 0)
```

**Target is newly introduced.** `WeierstrassCurve.tateEquivOfComponents` does not exist at the
pre-proof parent baseline:

```text
$ git grep -n 'tateEquivOfComponents' 1f6d11c -- FLT/.../TateCurve.lean   → (no match, exit 1)
```

There is therefore no earlier public signature for the target against which to assert literal
preservation; the correct statement is that its signature is unchanged since introduction at
`439c6b0`.

**Pre-existing public consumer signature preserved.** `WeierstrassCurve.tateEquiv` did exist at
the baseline (`1f6d11c:TateCurve.lean`), with body `sorry`:

```lean
variable [DecidableEq k] in
noncomputable def WeierstrassCurve.tateEquiv :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point :=
  sorry
```

At the frozen commit (`TateCurve.lean:451-463`) the identical `variable [DecidableEq k] in`
guard, name, binders, and target type are retained; only the body changed from `sorry` to the
component assembly `E.tateEquivOfComponents curveEquiv C E.exists_variableChange_tateCurve.choose_spec`.
No argument, instance, source, target, or namespace change was made to the public consumer.

**Elaborated target interface (fresh `#check`).** From the fresh scratch run (§6):

```text
@WeierstrassCurve.tateEquivOfComponents :
  {k : Type u_1} → [Field k] → [ValuativeRel k] → [TopologicalSpace k] →
  [IsNonarchimedeanLocalField k] → (E : WeierstrassCurve k) → [E.IsElliptic] →
  [WeierstrassCurve.HasSplitMultiplicativeReduction (↥(ValuativeRel.valuation k).integer) E] →
  [DecidableEq k] →
  Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (WeierstrassCurve.Affine.baseChange (tateCurve E.q) k).Point →
  (C : WeierstrassCurve.VariableChange k) → C • WeierstrassCurve.tateCurve E.q = E →
  Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (WeierstrassCurve.Affine.baseChange E k).Point
```

No `E.IsMinimal 𝒪[k]` instance leaks into the public target signature — independently confirmed.

## 5. Source proof and handoff inspection

**Target (`TateCurve.lean:435-448`).** The proof is a direction-correct transitive composition:

```lean
noncomputable def WeierstrassCurve.tateEquivOfComponents [DecidableEq k]
    (curveEquiv : Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ ((tateCurve E.q)⁄k).Point)
    (C : VariableChange k) (hC : C • tateCurve E.q = E) :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point := by
  letI : (tateCurve E.q).IsElliptic :=
    WeierstrassCurve.isElliptic_tateCurve E.qUnit E.valuation_q_lt_one
  exact curveEquiv.trans
    ((Affine.Point.equivVariableChange (tateCurve E.q) C).symm.trans (Affine.Point.equivOfEq hC))
```

Direction check, verified independently against
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`:

- `equivOfEq (h : V = V') : V.Point ≃+ V'.Point` (line 179).
- `equivVariableChange W C : (C • W).Point ≃+ W.Point` (line 209).
- Hence `(equivVariableChange (tateCurve E.q) C).symm : (tateCurve E.q).Point ≃+ (C • tateCurve E.q).Point`,
  and with `hC : C • tateCurve E.q = E`, `equivOfEq hC : (C • tateCurve E.q).Point ≃+ E.Point`.
- Composition: `Q ≃+ (tateCurve E.q).Point ≃+ (C • tateCurve E.q).Point ≃+ E.Point`, i.e. exactly
  the declared `Q ≃+ (E⁄k).Point`.

The ellipticity instance is supplied by the proved helper `isElliptic_tateCurve`
(`TateCurve.lean:425-433`), which itself audits clean (§6). Neither provider theorem is invoked
inside the target body; provider results enter only as explicit arguments `curveEquiv`, `C`, `hC`.
There is no `sorry` in the target block.

**Probe (`FLTMethodology/Probes/TateUniformizationAssembly.lean`).** Re-derives the same join
independently as `assembleTateEquiv` from an explicit `hTate` ellipticity argument (no analytic or
local-form theorem hidden), packages it as `nonempty_tateEquiv_of_components`, and prints the
axioms of four declarations. Contains no admission.

**Implementation handoff (lines 29-40).** States the bounded claim honestly: the algebraic join is
complete and audits to the standard trio, and `#print axioms WeierstrassCurve.tateEquiv` "still
honestly contains `sorryAx` through those admitted providers." Consistent with all findings below.

## 6. Independent builds and fresh axiom audit

**Build 1 — provider file (required):**

```text
$ lake build FLT.KnownIn1980s.EllipticCurves.TateCurve
⚠ [2814/2814] Built FLT.KnownIn1980s.EllipticCurves.TateCurve (5.6s)
Build completed successfully (2814 jobs).   EXIT=0
```

Only warnings: pre-existing unused-section-variable lints at `TateCurve.lean:694` and `:711`
(downstream torsion lemmas `tatePoint_mem_torsionBy_of_mem_rootsOfUnity` /
`tatePoint_mem_torsionBy_of_pow_eq`), unrelated to the target or its assembly proof.

**Build 2 — assembly probe (required):**

```text
$ lake build FLTMethodology.Probes.TateUniformizationAssembly
ℹ [2815/2815] Built FLTMethodology.Probes.TateUniformizationAssembly (2.5s)
Build completed successfully (2815 jobs).   EXIT=0
```

**Anti-cache measure.** Before the builds above I deleted the on-disk `.olean`/`.ilean`/`.c`/
`.trace` artifacts for both modules, forcing a genuine recompile. Lake reported `Built` (not
`Replayed`) for `TateCurve` (5.6s) and for the probe (2.5s), so the axiom lines emitted below are
from a fresh elaboration, not a cached info-replay.

**Fresh scratch `#print axioms`** (streamed via stdin; no scratch file written into the worktree),
run against the freshly recompiled oleans:

```text
$ lake env lean /dev/stdin <<'EOF'
import FLT.KnownIn1980s.EllipticCurves.TateCurve
#check @WeierstrassCurve.tateEquivOfComponents
#print axioms WeierstrassCurve.tateEquivOfComponents
#print axioms WeierstrassCurve.tateCurveEquiv
#print axioms WeierstrassCurve.exists_variableChange_tateCurve
#print axioms WeierstrassCurve.tateEquiv
#print axioms WeierstrassCurve.isElliptic_tateCurve
EOF

'WeierstrassCurve.tateEquivOfComponents'      depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.tateCurveEquiv'             depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.exists_variableChange_tateCurve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.tateEquiv'                  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.isElliptic_tateCurve'       depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

The same closures were also obtained in a first scratch run before the forced recompile, and in the
probe's fresh build output (`assembleTateEquiv`, `nonempty_tateEquiv_of_components`,
`tateEquivOfComponents` all `[propext, Classical.choice, Quot.sound]`; `tateEquiv` includes
`sorryAx`). Three independent observations agree.

## 7. Bounded closure vs. residual admissions (`sorryAx` inventory)

**Bounded target has no `sorryAx`.** `WeierstrassCurve.tateEquivOfComponents` and the proved helper
`WeierstrassCurve.isElliptic_tateCurve` both close on `[propext, Classical.choice, Quot.sound]`.

Complete `sorry` inventory in `TateCurve.lean` (independently greped): lines
`225, 344, 576, 589, 670, 684, 691, 740` (line 728 is a comment, not an admission). Mapping:

| Declaration | Location | Role | Axiom result | Disposition |
|---|---|---|---|---|
| `isElliptic_tateCurve` | `TateCurve.lean:425-433` | proved helper used by target | standard trio | closed |
| `tateEquivOfComponents` | `TateCurve.lean:435-448` | **bounded target** | standard trio | **closed (no `sorryAx`)** |
| `tateCurveEquiv` | `TateCurve.lean:223-225` | analytic provider | includes `sorryAx` | **ADMITTED (provider)** |
| `exists_variableChange_tateCurve` | `TateCurve.lean:342-344` | local-form provider | includes `sorryAx` | **ADMITTED (provider)** |
| `tateEquiv` | `TateCurve.lean:451-463` | aggregate consumer instantiating both providers | includes `sorryAx` | **NOT closed** |
| `tateEquiv_baseChange` | `:569-576` | downstream consumer | admitted (line 576) | outside contract |
| `tateEquiv_galois` | `:584-589` | downstream consumer | admitted (line 589) | outside contract |
| `tateEquivSepClosure` | `:668-670` | downstream consumer | admitted (line 670) | outside contract |
| `tatePoint_baseChange` | `:681-684` | downstream consumer | admitted (line 684) | outside contract |
| `tatePoint_galois` | `:688-691` | downstream consumer | admitted (line 691) | outside contract |
| `weilPairing_tatePoint` | `:734-740` | downstream consumer | admitted (line 740) | outside contract |

**Admitted providers (explicit, as required):** `WeierstrassCurve.tateCurveEquiv` and
`WeierstrassCurve.exists_variableChange_tateCurve`.

**Admitted consumers (explicit, as required):** the aggregate
`WeierstrassCurve.tateEquiv` (transitively, because it *chooses and supplies* the two provider
results into the target), plus `tateEquiv_baseChange`, `tateEquiv_galois`, `tateEquivSepClosure`,
`tatePoint_baseChange`, `tatePoint_galois`, and `weilPairing_tatePoint`.

The target is intentionally parametric in `curveEquiv`, `C`, `hC`; passing an admitted provider's
output into it later does not retroactively insert `sorryAx` into the target declaration — it
inserts it into the instantiating consumer, exactly as the aggregate `tateEquiv` closure shows.

**Do NOT promote the aggregate Tate equivalence.** It is **not** valid to infer from this review
that analytic Tate uniformization, the local-form classification, functoriality/Galois
compatibility, the separable-closure construction, Weil-pairing compatibility, or the aggregate
Tate–Frey component is complete. The only closure asserted is:

> Given an explicit Tate-curve additive equivalence and a variable change with the stated curve
> equality, `WeierstrassCurve.tateEquivOfComponents` constructs the desired equivalence to `E(k)`
> without `sorryAx`.

## 8. GPT-5.6 audit factual accuracy

Every checkable factual claim in the GPT audit was independently reproduced and is accurate:

- Identity commits, branch, and the three reviewed blob hashes (§1) — **match**.
- Toolchain/lake/lean versions and Mathlib pin (§2) — **match**.
- Target source text, location, and the direction-correct composition argument (§3) — **match**.
- `sorry` line list `225, 344, 576, 589, 670, 684, 691, 740` (§3) — **match**.
- Newly-introduced target has no pre-proof baseline; `git grep` exit 1 (§4) — **match**.
- Post-introduction diff empty, exit 0 (§4) — **match**.
- Public consumer `tateEquiv` signature unchanged; only body replaced (§4) — **match**.
- Elaborated target interface with no `IsMinimal` leak (§4) — **match**.
- Build results, job counts, and the two `694/711` lints (§5) — **match**.
- Fresh axiom closures for all five declarations (§6) — **match** (byte-for-byte).
- Provider/consumer role table (§7) — **match**.
- Statement that no `theorem-contracts.ndjson` was present in the worktree (§4, §8.4) —
  **independently confirmed true** (see §9).

Immaterial presentation notes (not errors): the GPT audit gives the target block as "435-448" in
§3 and "438-448" in the §7 table (docstring line 435 vs. `def` keyword line 438), and cites
`tateEquivSepClosure` as "665-670" where the `def` keyword is line 668 (665 is the docstring
start). Both are doc-block-vs-declaration boundary choices, not factual discrepancies. The GPT
verdict (PASS for the bounded contract, no promotion of providers/aggregate) is sound.

## 9. Contract-registry update — withheld (governance gap)

The instruction was: *if and only if the bounded target passes, update the
`THM-TATE-COMPONENT-ASSEMBLY` record in `methodology/control/theorem-contracts.ndjson`
(`review_status: reviewed`, `proof_status: remain kernel-clean`,
`residual_gap: admitted providers and consumer integration remain`).*

The bounded target passes. However, the update **cannot be performed**, because the target does
not exist:

```text
$ ls methodology/control/theorem-contracts.ndjson                 → No such file or directory
$ find . -not -path './.git/*' -not -path './.lake/*' -iname '*theorem-contract*'   → (none)
$ git ls-tree -r 160050be --name-only | grep -i theorem-contract  → (none in frozen tree)
$ grep -rn 'THM-TATE-COMPONENT-ASSEMBLY' methodology/             → only the two review reports
```

There is no `theorem-contracts.ndjson` file and no `THM-TATE-COMPONENT-ASSEMBLY` record anywhere
in the worktree or the frozen commit tree — the theorem ID appears only in the GPT audit and this
report. "Update the record" presupposes an existing record; none exists. Consistent with the
standing constraints (edit no proof source, probes, other theorem contracts, `.helios`, or task
files; work only inside this review directory), and because fabricating a control-registry file
with an invented schema in a governance directory is a hard-to-reverse action that would likely
diverge from the canonical registry maintained elsewhere, **the registry mutation was
deliberately withheld** rather than invented.

**Operator action required:** point this gate at the canonical `theorem-contracts.ndjson` (or
confirm creation is intended and specify the record schema) so the
`reviewed` / `remain kernel-clean` / `residual_gap: admitted providers and consumer integration
remain` fields can be written to the correct location. Until then the technical PASS stands on the
Lean evidence, but the contract state is not yet recorded.

## 10. Evidence summary

| Check | Result |
|---|---|
| HEAD = frozen commit `160050be` | ✅ |
| Reviewed source byte-identical to frozen commit (3 blobs) | ✅ |
| Post-introduction diff `439c6b0..HEAD` empty | ✅ |
| Target newly introduced; consumer `tateEquiv` public signature preserved | ✅ |
| No `IsMinimal` leak in target signature | ✅ |
| `lake build FLT.KnownIn1980s.EllipticCurves.TateCurve` | ✅ exit 0 (fresh Built) |
| `lake build FLTMethodology.Probes.TateUniformizationAssembly` | ✅ exit 0 (fresh Built) |
| Fresh scratch `#print axioms` (forced recompile, not replay) | ✅ |
| `tateEquivOfComponents` free of `sorryAx` | ✅ `[propext, Classical.choice, Quot.sound]` |
| Providers `tateCurveEquiv`, `exists_variableChange_tateCurve` admitted | ⚠️ carry `sorryAx` (expected) |
| Aggregate `tateEquiv` + downstream consumers admitted; not promoted | ⚠️ carry `sorryAx` (expected) |
| GPT audit factual accuracy | ✅ all checkable claims reproduced |
| Contract-registry update | ⛔ withheld — file/record absent (§9) |
| Working tree clean (only untracked `reviews/`); no proof/probe/contract/task/.helios edits | ✅ |

---

**FINAL: PASS** on the bounded theorem contract `WeierstrassCurve.tateEquivOfComponents`
(kernel-clean, no `sorryAx`, both required builds green, byte-identical to the frozen commit,
public signatures intact). The admitted providers `tateCurveEquiv` and
`exists_variableChange_tateCurve`, the aggregate consumer `tateEquiv`, and the downstream
consumers remain admitted (`sorryAx`) and are explicitly **not** promoted by this review. The
mandated `theorem-contracts.ndjson` registry update was not performed because the target file and
record do not exist in this worktree (§9); this requires operator resolution and does not alter
the technical PASS.
