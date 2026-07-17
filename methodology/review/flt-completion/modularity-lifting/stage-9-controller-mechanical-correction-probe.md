# Stage 9 — controller mechanical-correction probe

The controller independently compiled the corrected three-definition residual vocabulary outside the
repository.

Temporary file:

- `/private/tmp/FLTModularityResidualVocabularyCorrectedProbe.lean`

Command:

```text
lake env lean /private/tmp/FLTModularityResidualVocabularyCorrectedProbe.lean
```

Result: exit 0.

```text
'FLTMethodology.Taylor2018.IsAbsolutelyIrreducibleInResidualClosure_probe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'FLTMethodology.Taylor2018.IsCyclotomicAbsolutelyIrreducibleInResidualClosure_probe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'FLTMethodology.Taylor2018.ClosureImpliesClassAbsIrred_probe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The probe includes both required mechanical repairs: the Cyclotomic import and exact universe pin.
Verdict: `CORRECTED-SIGNATURES-KERNEL-GREEN`. This authorizes the bounded production attempt only.
