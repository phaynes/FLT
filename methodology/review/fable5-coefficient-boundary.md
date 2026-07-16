# Fable 5 review: Taylor coefficient boundary

Candidate: `4d83061fb62a4eb98b33b47015161784ad9c31c8`

Model: `claude-fable-5`. Mode: fresh, read-only, bounded signature review. Approximate elapsed
wall time: six minutes.

Verdict: **REVISE PROVISIONAL COEFFICIENT BOUNDARY**.

The representation-isomorphism and common-extension relations were accepted. The residual-model
predicate was not: `[Algebra R k]` also allowed a generic-fibre extension. The review required the
coefficient map to kill `IsLocalRing.maximalIdeal R`, and required Brauer--Nesbitt uniqueness plus
the fixed residual algebraic-closure instantiation to remain explicit dependencies.

The selected repair is the visible proposition

```lean
IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R k)
```

rather than a hidden independence or lattice-choice assumption. The repaired definition still
requires a later kernel-clean Brauer--Nesbitt/lattice-independence theorem.
