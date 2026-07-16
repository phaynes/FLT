# FLT-204 existing-adapter review

Date: 2026-07-16  
Reviewer: Claude Fable 5  
Reviewed commit: `a5710b7`  
Mode: independent, read-only, hostile contract and axiom-boundary review

## Verdict

`APPROVE`

No P0 or P1 finding was reported. The reviewer confirmed that the three clean aliases are
definitionally equal to the frozen boss contracts, that the three downstream adapters elaborate,
and that their axiom closures contain only Lean's standard classical axioms.

## P2 findings

The reviewer found two assurance weaknesses in the evidence file, not defects in the adapter
theorems:

1. The quarantine inventory did not enumerate all 17 contaminated declarations visible from
   `import FLT.Components.Existing`: `cyclic_base_change`, `knownin1980s`, and 15 public
   `TotallyDefiniteQuaternionAlgebra` declarations whose closure contains `knownin1980s`.
2. The axiom output was observational rather than regression-pinned. It omitted explicit checks for
   `B3_proof`, `B2_proof`, `B1_proof`, and `flt`.

## Resolution

`ExistingAdaptersAudit.lean` now:

- wraps every clean and quarantined `#print axioms` command in exact `#guard_msgs` output;
- pins `B4`, `B4_implies_B3`, `cyclic_base_change`, `B3_proof`, `B2_proof`, `B1_proof`, and `flt`;
- records the complete 15-declaration quaternion surface reported by the review; and
- distinguishes the sole observed `sorryAx`-only leak (`cyclic_base_change`) from declarations also
  carrying `knownin1980s`.

This repair deliberately does not expose the admitted boss providers through
`FLT.Components.Existing`. The module supplies only clean contract vocabulary and already-proved
downstream adapters. It does not claim that the unconditional provider side is complete.

## Task-gate adjudication

`PASS`

The existing-proof adapters are suitable as a provider-neutral integration boundary. The actual
FLT construction remains open above `BossB4`; the review does not upgrade the current public
theorem to an unconditional result.
