# Independent executable review — FLT rank-two Chebotarev adapter

Act as an independent mathematical and Lean reviewer. This is read-only: do not edit files, do not
commit, do not update task or graph state, and do not claim FLT completion.

Repository:
`/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730`

Production commit to review:
`3e418d5`

Base reviewed Brauer--Nesbitt milestone:
`8929b77866985a66fa7299c418a2fad2867cc606`

Review the exact production diff and current equivalents of:

- `FLT/GaloisRepresentation/CompatibleFamilyComparison.lean`
- `FLTMethodology/Probes/ChebotarevRankTwo.lean`
- `methodology/source-design/chebotarev.md`
- `methodology/evidence/probes/FLT-CHEBOTAREV-RANK-TWO-20260730.md`
- `methodology/SOURCE-REGISTER.md`
- `methodology/control/source-design.ndjson`

Independently execute at least:

```bash
git diff --check 8929b77866985a66fa7299c418a2fad2867cc606..3e418d5
lake build FLT.GaloisRepresentation.CompatibleFamilyComparison \
  FLTMethodology.Probes.ChebotarevRankTwo
lake build FLT FLTMethodology
```

Audit the printed axioms of every public theorem added in the module. Confirm or refute that each
has exactly the standard trio `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no
custom density axiom.

Mathematical review questions:

1. Is `conjugacySaturation` the correct set, and is `charpoly_conjugate` valid for the precise
   representation type?
2. Does the dense-set proof correctly extend trace and determinant separately, with `T2Space k`
   and rank two used at the right places?
3. Is `globalArithFrob` definitionally aligned with `GaloisRep.toLocal` and the repository's
   arithmetic-Frobenius normalization?
4. Is `RatArithmeticFrobeniusConjugacyDensity` the smallest honest missing arithmetic contract for
   the live base field `ℚ`, including every finite exceptional set?
5. Does the conditional conclusion honestly state `Nonempty (Representation.Equiv ...)` rather
   than equality, and are semisimplicity, rank, coefficient topology, and full charpoly equality
   all explicit?
6. Does `GaloisRepFamily.isCompatible_charFrob_eq` merely restate the existing definition, without
   laundering a second representation, semisimplicity, coefficient transport, or determinant?
7. Are the source and evidence packets accurate? In particular, do they refrain from claiming the
   density theorem, T2 authorization, full compatible-family closure, or FLT completion?
8. Identify any statement-strength, universe, topology, conjugacy, finite-exception, coefficient,
   naming, import-cycle, source-provenance, or control-state defect.

Fail closed. Return exactly one leading verdict: `PASS`, `REVISE`, or `NO-RESULT`, followed by
executed commands and outputs, axiom results, findings ordered by severity, and the exact honest
promotion boundary. `PASS` means only that the deterministic adapter may be classified as
kernel-clean and independently reviewed; it must not promote `FLT-CHEBOTAREV` itself to proved.
