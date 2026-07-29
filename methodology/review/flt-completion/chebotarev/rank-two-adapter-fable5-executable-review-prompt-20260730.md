# Fable 5 executable review — FLT rank-two Chebotarev adapter

This is an executable independent review, not a design or plan-mode task. Run the commands and
return a terminal verdict in this response. Do not promise a later synthesis.

Repository:
`/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730`

Candidate implementation/evidence commit: `ee0f49e`

Reviewed Brauer--Nesbitt base: `8929b77866985a66fa7299c418a2fad2867cc606`

Later commits may add review prompts or transcripts only. Verify that condition. Keep tracked source
read-only; build-artifact writes under `.lake` are allowed and expected.

First read both prior review results. They found the mathematics and sources sound but the GPT
review profile's read-only filesystem prevented its mandatory Lake commands. Independently decide;
do not copy their verdicts.

Execute at least:

```bash
git status --short
git rev-parse HEAD
git merge-base --is-ancestor ee0f49e HEAD
git diff --check 8929b77866985a66fa7299c418a2fad2867cc606..ee0f49e
git diff --name-status ee0f49e..HEAD
lake env lean --stdin < FLT/GaloisRepresentation/CompatibleFamilyComparison.lean
lake env lean --stdin < FLTMethodology/Probes/ChebotarevRankTwo.lean
lake env lean --stdin < FLT.lean
lake env lean --stdin < FLTMethodology.lean
lake build FLT.GaloisRepresentation.CompatibleFamilyComparison \
  FLTMethodology.Probes.ChebotarevRankTwo
lake build FLT FLTMethodology
```

The four direct `lean --stdin` commands are the independent compilation of the exact current
sources. The two Lake commands verify the repository build graph and umbrella targets. Do not add
`-H`: the controller has separately completed hash-checked targeted and umbrella builds, while a
read-only reviewer cannot legally rewrite every pinned dependency's hash artifact.

Audit all seven public theorems added in
`FLT/GaloisRepresentation/CompatibleFamilyComparison.lean` and require exactly
`[propext, Classical.choice, Quot.sound]`. Fail on `sorryAx`, a custom density axiom, a hidden
density witness, dirty tracked state, an unexpected post-candidate source diff, failed direct
elaboration, failed Lake command, or a mathematical/source defect.

Recheck:

1. conjugacy saturation and the chosen-representative counterexample;
2. trace/determinant continuity and exact use of rank two and `T2Space`;
3. arithmetic-Frobenius normalization and the `GaloisRep.toLocal` bridge;
4. every finite exceptional set in `RatArithmeticFrobeniusConjugacyDensity`;
5. semisimplicity, common coefficients, rank and `Nonempty Representation.Equiv` conclusion;
6. Gee Fact 2.27 versus Remark 2.31, Wiese Theorem 1.2.8/Corollary 1.2.9, and Taylor's comparison;
7. the exact honest boundary.

Return exactly one leading verdict: `PASS`, `REVISE`, or `NO-RESULT`, then commands/results, axiom
table, findings, and boundary. `PASS` approves only the deterministic adapter as kernel-clean and
independently reviewed. Density remains unwitnessed; no T2 density assumption is authorized;
`FLT-CHEBOTAREV`, its downstream compatible-family terminal, and FLT remain open.
