# THM-TATE-COMPONENT-ASSEMBLY — GPT-5.6 xhigh technical audit

**Date:** 2026-07-19  
**Task:** `task:ca-flt-thm-tate-component-assembly-review-20260719`  
**Role:** technical auditor only; not the independent approver  
**Target declaration:** `WeierstrassCurve.tateEquivOfComponents`  
**Verdict:** **PASS for the bounded theorem contract**

The declaration is a complete, kernel-clean algebraic assembly from two supplied component values.
Its independently reproduced axiom closure is exactly
`[propext, Classical.choice, Quot.sound]`; in particular, it does **not** contain `sorryAx`.
This verdict does not close either mathematical provider, the aggregate
`WeierstrassCurve.tateEquiv`, or any downstream Tate uniformization consumer.

No proof source, probe source, theorem-contract registry, task state, commit, or remote was changed
by this audit. The only intended tracked-worktree output is this report.

## 1. Frozen review identity

The audit was performed in:

```text
/Volumes/second-store/devel/proof-forks/FLT-tate-component-review-20260719
```

Initial identity commands and output:

```text
$ git status --short --branch
## codex/ca-flt-thm-tate-component-assembly-review-20260719

$ git rev-parse HEAD
160050be4d7066affd510f8076ca38f1f6980cf7

$ git branch --show-current
codex/ca-flt-thm-tate-component-assembly-review-20260719
```

Relevant commits:

- reviewed handoff commit: `160050be4d7066affd510f8076ca38f1f6980cf7`;
- proof-introduction commit: `439c6b022046736319ec88f4c457f696cb9fbf02`;
- pre-proof common baseline: `1f6d11caee718028bf783c968511d34865ffd9f0`.

The relevant reviewed blobs are:

```text
98551af43a86b7580dde6366f1e885de4861521a  FLT/KnownIn1980s/EllipticCurves/TateCurve.lean
61325b223e532cee46d34a987083bf762d0f26d2  FLTMethodology/Probes/TateUniformizationAssembly.lean
3dc289abefa7fb3ff7ea8aad2601382f91b673f7  methodology/review/flt-completion/tate-frey/implementation-handoff-20260719.md
```

The implementation handoff was inspected as evidence, not accepted as authority. Its bounded
claim at lines 29–40 was independently reproduced below.

## 2. Toolchain and dependency pin

Commands and output:

```text
$ sed -n '1p' lean-toolchain
leanprover/lean4:v4.32.0-rc1

$ lake --version
Lake version 5.0.0-src+b4812ae (Lean version 4.32.0-rc1)

$ lean --version
Lean (version 4.32.0-rc1, arm64-apple-darwin24.6.0,
commit b4812ae53eea93439ad5dce5a5c26591c31cb697, Release)
```

Mathlib is pinned identically in `lakefile.toml:22-24` and `lake-manifest.json:4-9`:

```text
https://github.com/leanprover-community/mathlib4.git
a3364faec42918fcd84a03a255b50570129f9ead
```

## 3. Exact source inspection

The target is at `FLT/KnownIn1980s/EllipticCurves/TateCurve.lean:435-448`:

```lean
/-- Assemble the uniformisation of a split-multiplicative curve from the explicit Tate-curve
uniformisation and a change of Weierstrass coordinates. This is the algebraic join: the analytic
uniformisation and local-form classification remain separate inputs. -/
noncomputable def WeierstrassCurve.tateEquivOfComponents [DecidableEq k]
    (curveEquiv :
      Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+
        ((tateCurve E.q)⁄k).Point)
    (C : VariableChange k) (hC : C • tateCurve E.q = E) :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point := by
  letI : (tateCurve E.q).IsElliptic :=
    WeierstrassCurve.isElliptic_tateCurve E.qUnit E.valuation_q_lt_one
  exact curveEquiv.trans
    ((Affine.Point.equivVariableChange (tateCurve E.q) C).symm.trans
      (Affine.Point.equivOfEq hC))
```

The proof is type- and direction-correct:

1. Lines 444–445 construct the required ellipticity instance for `tateCurve E.q` using the
   proved `isElliptic_tateCurve`; this helper independently audits without `sorryAx`.
2. `curveEquiv` maps the quotient to the Tate curve's affine point group.
3. `Affine.Point.equivVariableChange W C` has direction `(C • W).Point ≃+ W.Point`
   (`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:207-223`). Its inverse therefore
   maps the points of `tateCurve E.q` to the points of `C • tateCurve E.q`.
4. `Affine.Point.equivOfEq hC` transports those points along
   `hC : C • tateCurve E.q = E` to `(E⁄k).Point`.
5. Thus the two transitive compositions have exactly the declared source and target. Neither
   provider theorem is invoked by this declaration; provider results enter only as explicit
   arguments.

There is no `sorry` in the target block. The direct `sorry` search in the surrounding provider
file found admissions only at lines `225, 344, 576, 589, 670, 684, 691, 740` at the reviewed
commit; their scope is separated in section 7.

## 4. Signature and history audit

The target name did not exist at the discoverable pre-proof baseline:

```text
$ git grep -n 'tateEquivOfComponents' \
    1f6d11caee718028bf783c968511d34865ffd9f0 -- \
    FLT/KnownIn1980s/EllipticCurves/TateCurve.lean
BASELINE_TARGET_GREP_EXIT=1
```

Therefore there is no earlier public signature for this newly introduced target against which to
claim literal preservation. It was introduced at `439c6b0...` and its source and probe have not
changed between that introduction and the reviewed commit:

```text
$ git diff --exit-code \
    439c6b022046736319ec88f4c457f696cb9fbf02..HEAD -- \
    FLT/KnownIn1980s/EllipticCurves/TateCurve.lean \
    FLTMethodology/Probes/TateUniformizationAssembly.lean
POST_INTRODUCTION_DIFF_EXIT=0
```

The pre-existing public consumer `WeierstrassCurve.tateEquiv` *does* have a discoverable baseline.
At `1f6d11c...:TateCurve.lean:334-341` its type was:

```lean
variable [DecidableEq k] in
noncomputable def WeierstrassCurve.tateEquiv :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point :=
  sorry
```

At the reviewed commit, lines 450–463 retain exactly that explicit signature and replace only the
body with the component assembly. No argument, instance, source, target, or namespace change was
made to the public consumer signature.

The elaborated target interface was independently checked with
`#check @WeierstrassCurve.tateEquivOfComponents`. Abbreviating Lean's fully qualified universe
printing without changing its binders, it is:

```text
{k : Type u} → [Field k] → [ValuativeRel k] → [TopologicalSpace k] →
[IsNonarchimedeanLocalField k] →
(E : WeierstrassCurve k) → [E.IsElliptic] →
[E.HasSplitMultiplicativeReduction 𝒪[k]] → [DecidableEq k] →
(Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ ((tateCurve E.q)⁄k).Point) →
(C : VariableChange k) → C • tateCurve E.q = E →
Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point
```

Notably, no `E.IsMinimal 𝒪[k]` instance leaks into the public target signature.

No `theorem-contracts.ndjson` was present in this review worktree or discoverable in the adjacent
FLT worktrees, so no separate registry-signature comparison was possible. No such registry was
created or edited. The contract assessed here is the task-named declaration and its frozen Lean
interface.

## 5. Narrow Lean builds

This worktree initially lacked decompressed Mathlib object artifacts. A first cold invocation of
the same TateCurve target began compiling the pinned dependency graph and was deliberately
interrupted before it could serve as verdict evidence:

```text
$ lake build FLT.KnownIn1980s.EllipticCurves.TateCurve
...
✔ [724/2820] Built Mathlib.Algebra.EuclideanDomain.Field (3.1s)
^C
EXIT=130
```

This was an environment-bootstrap interruption, not a theorem failure. The pinned repository cache
was then materialized:

```text
$ lake exe cache get
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
Decompressing 7813 already-cached file(s) (821 already decompressed)
No files to download
Decompressed 7813 already-cached file(s)
Completed successfully in 23897 ms!
EXIT=0
```

### 5.1 Exact provider-file target

```text
$ /usr/bin/time -p lake build FLT.KnownIn1980s.EllipticCurves.TateCurve
✔ [2809/2814] Built FLT.Mathlib.Algebra.Polynomial.QuadraticDiscriminant (2.4s)
✔ [2810/2814] Built FLT.KnownIn1980s.EllipticCurves.TateParameter (3.5s)
✔ [2811/2814] Built FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange (3.6s)
✔ [2812/2814] Built FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction (5.8s)
✔ [2813/2814] Built FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange (3.2s)
⚠ [2814/2814] Built FLT.KnownIn1980s.EllipticCurves.TateCurve (6.4s)
Build completed successfully (2814 jobs).
real 21.94
user 36.61
sys 8.39
EXIT=0
```

The only warnings were existing unused-section-variable lints at `TateCurve.lean:694` and `:711`.
They concern downstream torsion lemmas, not the target or its assembly proof.

### 5.2 Required assembly probe

```text
$ /usr/bin/time -p lake build FLTMethodology.Probes.TateUniformizationAssembly
⚠ [2814/2815] Replayed FLT.KnownIn1980s.EllipticCurves.TateCurve
ℹ [2815/2815] Built FLTMethodology.Probes.TateUniformizationAssembly (5.7s)
info: FLTMethodology/Probes/TateUniformizationAssembly.lean:59:0:
  'TateUniformizationAssemblyProbe.assembleTateEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/TateUniformizationAssembly.lean:60:0:
  'TateUniformizationAssemblyProbe.nonempty_tateEquiv_of_components' depends on axioms:
  [propext, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/TateUniformizationAssembly.lean:61:0:
  'WeierstrassCurve.tateEquivOfComponents' depends on axioms:
  [propext, Classical.choice, Quot.sound]
info: FLTMethodology/Probes/TateUniformizationAssembly.lean:62:0:
  'WeierstrassCurve.tateEquiv' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
Build completed successfully (2815 jobs).
real 7.70
user 2.98
sys 3.40
EXIT=0
```

The probe itself was inspected at `FLTMethodology/Probes/TateUniformizationAssembly.lean:1-64`.
Lines 32–44 independently assemble the same change-of-variables join from an explicit ellipticity
argument; lines 47–57 package it as `Nonempty`; lines 59–62 print the axiom closures. It contains
no admission and the build above reran it successfully.

## 6. Independent scratch signature and axiom audit

The following scratch input was streamed to Lean through stdin; no scratch file was written into
the worktree:

```text
$ lake env lean /dev/stdin <<'EOF'
import FLT.KnownIn1980s.EllipticCurves.TateCurve

set_option pp.universes true in
#check @WeierstrassCurve.tateEquivOfComponents

#print axioms WeierstrassCurve.isElliptic_tateCurve
#print axioms WeierstrassCurve.tateEquivOfComponents
#print axioms WeierstrassCurve.tateCurveEquiv
#print axioms WeierstrassCurve.exists_variableChange_tateCurve
#print axioms WeierstrassCurve.tateEquiv
EOF
```

The signature output has been recorded in section 4. The complete axiom output was:

```text
'WeierstrassCurve.isElliptic_tateCurve' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.tateEquivOfComponents' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.tateCurveEquiv' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.exists_variableChange_tateCurve' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
'WeierstrassCurve.tateEquiv' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
EXIT=0
```

This independent scratch run is the decisive bounded closure evidence: the target's transitive
axiom set excludes `sorryAx` even though each named provider and the instantiated aggregate
consumer includes it.

## 7. Bounded closure versus residual admissions

| Declaration | Source | Role | Axiom result | Bounded disposition |
|---|---:|---|---|---|
| `isElliptic_tateCurve` | `TateCurve.lean:425-433` | proved helper used by target | standard trio | closed |
| `tateEquivOfComponents` | `TateCurve.lean:438-448` | target assembly | standard trio | **closed** |
| `tateCurveEquiv` | `TateCurve.lean:223-225` | analytic provider | includes `sorryAx` | open, outside target proof |
| `exists_variableChange_tateCurve` | `TateCurve.lean:342-344` | local-form provider | includes `sorryAx` | open, outside target proof |
| `tateEquiv` | `TateCurve.lean:455-463` | aggregate consumer instantiating both providers | includes `sorryAx` | not closed by this audit |

The target is intentionally parametric in `curveEquiv`, `C`, and `hC`. Passing an admitted
provider's output to the target later does not retroactively put that provider's `sorryAx` in the
target declaration; it puts the axiom in the instantiated consumer, exactly as the scratch audit
shows.

Additional admitted downstream consumers in the same file are also outside this theorem contract:

- `tateEquiv_baseChange` at lines 569–576;
- `tateEquiv_galois` at lines 584–589;
- `tateEquivSepClosure` at lines 665–670;
- `tatePoint_baseChange` at lines 680–684;
- `tatePoint_galois` at lines 688–691;
- the Weil-pairing compatibility theorem ending at line 740.

Accordingly, the valid closure statement is only:

> Given the explicit Tate-curve additive equivalence and a variable change with the stated curve
> equality, `WeierstrassCurve.tateEquivOfComponents` constructs the desired equivalence to `E(k)`
> without `sorryAx`.

It is **not** valid to infer that analytic Tate uniformization, the local classification,
functoriality/Galois compatibility, the separable-closure construction, Weil-pairing compatibility,
or the aggregate Tate–Frey component is complete.

## 8. Residual gaps and non-blocking observations

1. The two mathematical provider leaves remain admitted, as explicitly demonstrated above.
2. The aggregate `tateEquiv` remains transitively admitted because it chooses and supplies those
   two provider results.
3. The direct target build emitted only two unrelated linter warnings in downstream lemmas; there
   was no target warning or error.
4. A separate theorem-contract registry was not discoverable in this worktree, so the only
   signature-preservation statement possible for the target itself is that it is unchanged since
   introduction. The older public consumer signature was discoverable and is unchanged.
5. This report is technical evidence only. No approval, task submission, merge, commit, or push was
   performed.

None of these residuals defeats the bounded target theorem contract.

## 9. Final verdict and git state

**PASS** — `WeierstrassCurve.tateEquivOfComponents` elaborates at the frozen commit, has the
intended composition and public interface, survives both the narrow provider-file build and the
required probe build, and independently audits with no `sorryAx`.

Pre-report git status was clean. After creating the sole authorized report, the expected final
status is the review branch plus this one untracked evidence file; no proof or contract source is
modified:

```text
$ git status --short --branch --untracked-files=all
## codex/ca-flt-thm-tate-component-assembly-review-20260719
?? methodology/evidence/reviews/THM-TATE-COMPONENT-ASSEMBLY-GPT-TECHNICAL-AUDIT-20260719.md
```
