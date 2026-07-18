# Operator adjudication and conditional coefficient build

Date: 2026-07-18  
Operator: philip.haynes  
Decision: Option 1 — accept an explicit seventh open T1 provider.

## Disposition

The field-of-definition datum is tracked as the new open obligation
`FLT-MLT-COEFF-REALIZATION`. It is a dependency of `FLT-MLT-COEFFICIENTS`; it is not an
axiom, admission, historical assumption, or completed theorem. The coefficient obligation remains
`definition-gap`.

The bounded coefficient vocabulary is persisted in
`FLTMethodology/Probes/MLTCoefficientData.lean`. It includes:

- stable-lattice and coefficient-data structures;
- the generic closure tower and residual-closure comparison vocabulary;
- same-coefficient-ring characteristic-polynomial comparison;
- conditional Brauer–Nesbitt wiring;
- base-change-through-a-tower and conjugation transport;
- `NamedClosureRealization`, the exact open provider predicate; and
- `exists_descent_to_named_consumer`, which composes `exists_closure_descent` only after a
  caller supplies `NamedClosureRealization`.

No declaration constructs the missing realization unconditionally.

## Kernel gate

Commands:

```text
lake build FLTMethodology.Probes.MLTCoefficientData
lake env lean /private/tmp/MLTCoefficientDataCommandAudit.lean
```

Both commands passed. Every one of the 23 persisted declarations reported exactly:

```text
[propext, Classical.choice, Quot.sound]
```

In particular:

```text
'FLTMethodology.Taylor2018.Coefficients.NamedClosureRealization'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'FLTMethodology.Taylor2018.Coefficients.exists_closure_descent'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'FLTMethodology.Taylor2018.Coefficients.exists_descent_to_named_consumer'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `knownin1980s`, custom realization axiom, `admit`, `unsafe`, or
`native_decide` was introduced by this tranche.

## Control transition

- New node: `FLT-MLT-COEFF-REALIZATION`, state `definition-gap` (OPEN).
- New edge: `FLT-MLT-COEFF-REALIZATION → FLT-MLT-COEFFICIENTS`.
- `FLT-MLT-COEFFICIENTS`: remains `definition-gap`; no promotion.
- Component disposition: operator-adjudicated bounded slice green, seven providers open.
- Operator note: “operator chose option 1 (accept 7th provider) 2026-07-18; realization tracked as
  open T1 provider; research operator-side; no promotion.”

The graph and Helios projection are regenerated after this packet is written.
