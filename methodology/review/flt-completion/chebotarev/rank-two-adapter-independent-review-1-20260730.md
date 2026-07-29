# Independent executable review — first result

Agent: `gpt56xhigh-independent-reviewer-d10`

Model: `gpt-5.6-sol`

Effort: `xhigh`

Elapsed: `509192 ms`

Production commit reviewed: `3e418d53b6de47dacf976a43f5416267e7b94751`

Whitespace-normalized response follows; wording is exact. The byte-exact transcript remains in the
session ledger named by this task's evidence record.

REVISE

## Executed commands and outputs

Repository state:

```text
HEAD: 22576572cfeddb387d35f24480981124d224b2ef
production: 3e418d53b6de47dacf976a43f5416267e7b94751
base: 8929b77866985a66fa7299c418a2fad2867cc606
worktree: clean
```

`3e418d5` is an ancestor of HEAD. The only later change is an independent-review prompt; all six requested current files are byte-identical to production.

```text
git diff --check 8929b77866985a66fa7299c418a2fad2867cc606..3e418d5
exit 2

methodology/evidence/probes/FLT-CHEBOTAREV-RANK-TWO-20260730.md:3: trailing whitespace
methodology/evidence/probes/FLT-CHEBOTAREV-RANK-TWO-20260730.md:4: trailing whitespace
methodology/evidence/probes/FLT-CHEBOTAREV-RANK-TWO-20260730.md:69: new blank line at EOF
methodology/review/flt-completion/chebotarev/stage-1-gpt56xhigh-repository-only-design-20260730.md:213: new blank line at EOF
methodology/source-design/chebotarev.md:3: trailing whitespace
methodology/source-design/chebotarev.md:4: trailing whitespace
methodology/source-design/chebotarev.md:84: new blank line at EOF
```

Targeted build:

```text
lake build FLT.GaloisRepresentation.CompatibleFamilyComparison \
  FLTMethodology.Probes.ChebotarevRankTwo

exit 0
Build completed successfully (3629 jobs).
```

Exact production sources were also re-elaborated directly, avoiding cached-source ambiguity:

```text
lake env lean --stdin < FLT/GaloisRepresentation/CompatibleFamilyComparison.lean
exit 0

lake env lean --stdin < FLTMethodology/Probes/ChebotarevRankTwo.lean
exit 0
```

Umbrella build:

```text
lake build FLT FLTMethodology
exit 1

✖ Building FLT
error: failed to remove output artifacts: operation not permitted
file: .../.lake/build/lib/lean/FLT.olean
Some required targets logged failures:
- FLT
error: build failed
```

`.lake/build` is a read-only symlink to the tested-baseline build. The final [FLT.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT.lean:58) is newer than the cached `FLT.olean`, so the evidence packet’s recorded umbrella success does not seal the final root import. Both current umbrella source files nevertheless elaborate successfully through stdin:

```text
lake env lean --stdin < FLT.lean
exit 0

lake env lean --stdin < FLTMethodology.lean
exit 0
```

## Axiom audit

The module contains exactly seven public theorems, and the probe covers all seven. Each independently printed exactly:

```text
[propext, Classical.choice, Quot.sound]
```

| Theorem | Result |
|---|---|
| `charpoly_conjugate` | exact standard trio |
| `charpoly_eq_of_dense_of_finrank_eq_two` | exact standard trio |
| `nonempty_equiv_of_dense_charpoly_eq` | exact standard trio |
| `nonempty_equiv_of_dense_conjugacy_charpoly_eq` | exact standard trio |
| `charpoly_globalArithFrob` | exact standard trio |
| `nonempty_representationEquiv_of_charFrob_eq_of_density` | exact standard trio |
| `GaloisRepFamily.isCompatible_charFrob_eq` | exact standard trio |

No `sorryAx` and no custom density axiom enters any added theorem’s dependency closure. `FrobeniusConjugacyDensityAt` and `RatArithmeticFrobeniusConjugacyDensity` are proposition definitions, not axioms or witnesses.

## Findings, ordered by severity

1. **High — independent umbrella/build evidence is not sealed.**

   The required umbrella command fails because its final artifact cannot be replaced. More importantly, the cached `FLT.olean` predates final `FLT.lean`, while the [evidence packet](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/evidence/probes/FLT-CHEBOTAREV-RANK-TWO-20260730.md:25) records an umbrella success without recording production SHA `3e418d5`. Direct root elaboration passes, so this is not evidence of a Lean source failure, but a fresh writable umbrella build at the exact production SHA is required for promotion.

2. **Medium — the mandatory production diff check fails.**

   The seven whitespace/EOF findings above make the production diff mechanically non-green. Some trailing spaces are Markdown hard breaks, but they still fail the exact requested command.

3. **Low — stale declaration name in the axiom probe documentation.**

   [ChebotarevRankTwo.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLTMethodology/Probes/ChebotarevRankTwo.lean:12) refers to nonexistent `ChebotarevDensityContract`; the actual declaration is `RatArithmeticFrobeniusConjugacyDensity`.

4. **Low — source locator precision.**

   Wiese’s SHA-matched PDF confirms arithmetic Frobenius, conjugacy, finite Chebotarev, and the finite-quotient density argument. Gee Fact 2.27 states density; the explicit Chebotarev–Brauer–Nesbitt comparison is Gee Remark 2.31, not Fact 2.27 alone. The [source packet](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/source-design/chebotarev.md:30) should distinguish those locators. Its admission that an exact primary-source locator remains open is accurate.

5. **Low — graph vocabulary remains deliberately stale/open.**

   The main [FLT-CHEBOTAREV obligation](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/control/proof-obligations.ndjson:29) still names proposed `equal_of_charFrob_eq` and remains `absent`, `revision-required`. That correctly prevents promotion, but must eventually be split/rebound before obligation closure. The reviewed [source-design row](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/control/source-design.ndjson:15) is valid JSON and honestly says provider open.

## Mathematical conclusions

No substantive statement, universe, topology, conjugacy, finite-exception, coefficient, or import-cycle defect was found in the adapter itself:

- `conjugacySaturation` is the correct union of conjugacy classes. It defeats the finite-`S₃` chosen-representative counterexample.
- `charpoly_conjugate` correctly realizes `ρ(xgx⁻¹)` as linear conjugation for the precise `Representation k G V` type.
- Trace and determinant are separately continuous and extended using `T2Space k`; rank two is used for determinant extraction and characteristic-polynomial reconstruction.
- `globalArithFrob` is definitionally the map used by `GaloisRep.toLocal`. The repository definition is arithmetic Frobenius, acting by the residue-field `q`-power map.
- `RatArithmeticFrobeniusConjugacyDensity` is an honest representation-free `ℚ`-specialized contract quantified over every finite exceptional set.
- The conclusion is correctly `Nonempty (Representation.Equiv ...)`. Same coefficients, Hausdorff topology, two rank hypotheses, two semisimplicity hypotheses, and full characteristic-polynomial equality are explicit.
- `isCompatible_charFrob_eq` is only a definitional restatement. It introduces no second representation, semisimplicity, coefficient transport, determinant equality, or consumer closure.
- The source/evidence packets do not claim a density witness, T2 authorization, compatible-family closure, or FLT completion.
- The T2 register authorizes no Chebotarev axiom; T3 still requires a standard-trio density proof.

## Exact honest promotion boundary

Do not promote this review as `PASS`, and do not mark `FLT-CHEBOTAREV` proved.

After correcting the diff-check and naming defects and obtaining a fresh writable `lake build FLT FLTMethodology` sealed to `3e418d5`, the deterministic adapter alone may be classified as kernel-clean and independently reviewed.

Even then:

- `RatArithmeticFrobeniusConjugacyDensity` remains unwitnessed;
- no Chebotarev T2 assumption is authorized;
- T3 requires a standard-trio density proof;
- fixed-coefficient, determinant, semisimplicity, and consumer-specific family wiring remain open;
- `FLT-CHEBOTAREV`, the compatible-family terminal, and FLT remain unproved.

No files or control state were changed.
