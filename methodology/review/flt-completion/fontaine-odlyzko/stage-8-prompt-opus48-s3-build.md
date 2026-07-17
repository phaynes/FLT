OPUS 4.8 BOUNDED BUILD — FONTAINE--ODLYZKO S3 REDUCIBILITY

Implement only the independently accepted S3 production slice. Repository writes are authorized only
for:

- a new `FLTMethodology/Probes/FontaineOdlyzkoReducibility.lean`;
- its import in `FLTMethodology.lean`.

Do not edit control files, task state, any theorem under `FLT/`, or git state. The controller will
perform governance and commits after the build.

Read:

- `methodology/review/flt-completion/fontaine-odlyzko/stage-6-controller-s3-probe.md`;
- `methodology/review/flt-completion/fontaine-odlyzko/stage-7-gpt56xhigh-s3-review.md`;
- `/tmp/FontaineS3Probe.lean`.

Persist exactly the bounded five-declaration slice:

1. `ReducibleRankTwoData`;
2. `exists_reducibleRankTwoData`;
3. `ReducibleRankTwoData.quotientRepresentation`;
4. `ReducibleRankTwoData.quotient_surjective`;
5. `ReducibleRankTwoData.quotient_equivariant`.

You may replace the Slop irreducibility helper with the direct `IsSimpleOrder` argument if and only
if the result remains shorter, exact, and kernel-clean. Do not persist `quotientEquiv`,
`quotientFunctional`, either character, or any claim of trivial quotient action in this tranche.

Add `#check` and `#print axioms` for all five declarations. Run:

```text
lake build FLTMethodology.Probes.FontaineOdlyzkoReducibility
lake build FLTMethodology
```

PASS requires both builds green and every declaration to depend exactly on
`[propext, Classical.choice, Quot.sound]`. Return `BUILT-BOUNDED-S3`, `REVISE`, or
`OBSTRUCTION`, with the exact diff, build output, axiom output, and first residual goal. Do not
promote the full Fontaine--Odlyzko obligation.
