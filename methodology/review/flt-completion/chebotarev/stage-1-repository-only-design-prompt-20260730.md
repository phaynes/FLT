# Repository-only design: rank-two Chebotarev comparison

Work read-only. Do not edit the repository. Do not open any external literature
cache or QMD paper. Use only the Lean repository, pinned Mathlib, the current
obligation graph, and mathematical knowledge already available to you.

Design the smallest sound implementation increment for `FLT-CHEBOTAREV` after
the proved rank-two Brauer–Nesbitt milestone at commit `8929b77`. The encoded
compatible family is `GaloisRepFamily ℚ E 2`. The required mathematical passage
is from characteristic-polynomial agreement on all but finitely many unramified
Frobenius elements to agreement on every global Galois element, then application
of `nonempty_representationEquiv_of_finrank_eq_two`.

Inspect exact current types for `GaloisRep`, `GaloisRepFamily.isCompatible`,
`GaloisRep.toLocal`, `GaloisRep.charFrob`, absolute-Galois maps, arithmetic
Frobenius, module topology, determinant/trace continuity, and the new rank-two
provider. Search pinned Mathlib before declaring anything absent.

Return:

1. the exact strongest theorem that can be proved now without Chebotarev;
2. an exact named contract for the genuinely missing density theorem, with no
   representation-theoretic conclusion folded into it;
3. a dependency-ordered Lean declaration graph and candidate signatures;
4. the topology/conjugacy/coefficient/finite-exception pitfalls;
5. which part may be a named T2 historical assumption and which part must be
   standard-trio proof for T3;
6. a concrete build plan and stop-loss conditions.

Challenge the premise if the graph's proposed comparison type is still too
broad or does not match the available global/local Frobenius maps. Do not claim
Chebotarev, a compatible-family theorem, or FLT is proved.
