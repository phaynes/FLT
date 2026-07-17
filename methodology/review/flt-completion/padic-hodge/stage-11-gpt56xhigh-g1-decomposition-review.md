# Stage 11 — GPT-5.6 xhigh G1 decomposition review

Verdict: `REVISE-SUBSTANTIVE`, not obstruction.

## Confirmed

- The pin contains no `A_cris`, `B_cris`, `D_cris`, or representation-theoretic crystalline
  predicate. Existing “crystalline” hits concern divided-power/cohomology documentation.
- `IsPlaceAbove` is a viable small definition and standard-trio clean after adding the prime
  hypothesis. Without it, the `ell = 0` case is tautological.
- A scalar-compatible diagonal tensor-action combinator is a viable small unit.

## Required repairs

1. The proposed diagonal action assumptions are insufficient. Lean needs both
   `SMulCommClass Gamma E B` and `SMulCommClass Gamma E V`; with them, the tensor automorphism
   compiles with the exact standard trio.
2. Invariant-module scalar closure does not synthesize automatically. Commutation between `Gamma`
   and `FixedPoints.subring Gamma B` on the tensor product must be explicitly proved.
3. The generic coefficient story for `IsCrystallineRel` is wrong beyond `E = Q_l`. For finite
   coefficient extensions, standard `D_cris` is over `K0 tensor E`, or dimensions must be taken
   after restricting scalars to `Q_l`; one cannot simultaneously tensor over arbitrary `E` and
   identify fixed scalars with `K0`.
4. The dependency closure omits the local `C_p`/Galois-action bridge and a PD-envelope-of-an-ideal
   API, which is absent at the pin.
5. Fontaine’s `t` must not be described as a generator of `ker theta`.
6. `D_cris` may be defined after `B_cris`, its `K0` action, and the diagonal action. The theorem
   `B_cris^Gamma = K0` remains a later provider and must not be placed in parameter data.

## Bounded disposition

The smallest presently bankable unit is corrected `IsPlaceAbove` plus the scalar-compatible
diagonal tensor-action combinator. The first residual is the invariant `K0`-submodule construction
and its scalar-closure proof. No `IsCrystallineAt`, `D_cris` comparison theorem, or full p-adic-Hodge
promotion is authorized.

Action-costing: 609595 ms; input 8169439; cached input 7940096; output 29024; reasoning 16709; total
8198463 tokens. Session `019f7256-cfd7-7a33-a468-3a80ec9a6af5`.
