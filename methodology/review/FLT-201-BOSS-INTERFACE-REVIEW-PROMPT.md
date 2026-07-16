# Independent hostile review: clean FLT boss interface

Review the current branch in `/Volumes/second-store/devel/proof-forks/FLT` read-only. Do not edit,
commit, push, or create repository files. Temporary probes outside the repository are allowed.

The bounded review target is commit `324fa8314835c1eeccf5dd09c1c8b5fb008b7c70`, specifically:

- `FLT/Components/BossInterface.lean`
- `FLT/Basic/Lemmas.lean`
- `FLT/FreyCurve/FreyPackage.lean`
- `FLT/Proof.lean`
- `FLT/FreyCurve/Mazur.lean`
- `FLT/EllipticCurve/Torsion.lean`
- `methodology/evidence/contracts/BossInterfaceAudit.lean`

Context: the concrete repository `B4` type mentions `WeierstrassCurve.galoisRep`, whose present
dependency closure includes admitted torsion data. A theorem conditional on that concrete `B4`
therefore retains `sorryAx` even if its body is otherwise complete. The new module instead exposes
two abstract predicates on `FreyPackage`, providers for both predicates, and their incompatibility.
It derives `IsEmpty FreyPackage` and then the exact Mathlib `FermatLastTheorem` type.

Perform these checks:

1. Build `FLT.Components.BossInterface` and compile the audit file.
2. Confirm the exact types and axiom closures of both exported theorems.
3. Check that the module imports no provider implementation, generic `knownin1980s`, admitted
   representation data, `FLT.Proof`, or concrete `B4` definition.
4. Decide whether `FreyContradictionInterface` is a mathematically honest conditional boundary.
   In particular, distinguish an explicit conditional integration interface from an unconditional
   FLT proof.
5. Look for vacuity, hidden assumptions, a weaker endpoint, universe/type mistakes, or a route by
   which an arbitrary interface instance could be mistaken for a concrete FLT provider.
6. Assess minimality: identify any field unnecessary for the two exported theorems, and identify any
   semantic field that must be added now rather than deferred to the separately audited concrete
   Frey adapter.
7. Evaluate this acceptance criterion: "Clean shared mathematical vocabulary elaborates without
   generic knownin1980s, sorryAx, provider imports, or admitted data hidden in interface types."

Return exactly:

- `VERDICT: APPROVE` or `VERDICT: REVISE`
- `AXIOM AUDIT:` with the observed closures
- `P0/P1 FINDINGS:` or `NONE`
- `P2 FINDINGS:` or `NONE`
- `INTERFACE HONESTY:` one concise paragraph
- `TASK-GATE ADJUDICATION:` pass/fail with precise reason
- `NEXT ADAPTER OBLIGATION:` the smallest exact property the later concrete adapter must establish

Do not praise style. Do not infer that FLT is proved. Treat any inability to reproduce the kernel
commands as a review failure rather than substituting source inspection.
