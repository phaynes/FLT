# Fable 5 review: Brauer--Nesbitt boundary

Candidate: `d414ef1`.

Model: `claude-fable-5`. Mode: fresh, read-only, bounded mathematical and Lean-signature review.
Approximate elapsed wall time: twelve minutes. The bridge did not expose an exact elapsed field.

Verdict: **REVISE BRAUER-NESBITT BOUNDARY**.

Kernel evidence was independently reproduced: the boundary probe builds, and the proved trace
helper, finite counterexample, and consumer bridge have axiom closure
`[propext, Classical.choice, Quot.sound]`.

Load-bearing findings:

- `GroupContract` is a true arbitrary-field Brauer--Nesbitt statement. No field, group-finiteness,
  continuity, or finite-image hypothesis must be added.
- `SimpleCharactersLinearIndependentContract` is correctly parenthesized and true, but is the
  first missing terminal only for the algebraically closed specialization.
- `AlgClosedTwoDimensionalTraceContract` is true, but it cannot close the current generic
  `SemisimplifiedResidualModelsUnique` consumer without a separately reviewed narrowing.
- The finite `ZMod 2` regression refutes only the one-sided trace weakening.
- The consumer bridge is sufficient and non-circular; it does not prove necessity or minimality.
- Wiese's separable splitting-field proof sketch is incomplete over imperfect fields. The
  arbitrary-field proof needs a finite-dimensional joint-image/spanning-set argument or a separate
  component-wise descent proof.

Required action: retain `GroupContract`, correct the evidence and route description, and keep
`FLT-BRAUER-NESBITT` open. No repository file was modified by the reviewer.
