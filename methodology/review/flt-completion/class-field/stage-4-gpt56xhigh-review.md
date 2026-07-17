REVISE

The carrier and same-local-carrier repairs are correct, but the design does not resolve every Stage-2 finding.

| Finding | Result |
|---|---|
| 1. Nontrivial rank-one carrier | Resolved: `[Nontrivial A]` and `GaloisRep F A A` exclude the `ZMod 1` counterexample. |
| 2. Same-carrier local relation | Resolved: it reuses [`GaloisRep.toLocal`](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/RepresentationTheory/GaloisRep.lean:305) and remains only an equality relation, not globalization. |
| 3. Skinner–Wiles routing | Resolved at design level: moved to `FLT-AUX-LOCAL-FIELD`, with the missing MLT/graph relationship explicitly exposed. The live graph still has only the induced-modularity and auxiliary-curve edges ([proof-graph.ndjson](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-graph.ndjson:88)). |
| 4. Induction bookkeeping | Resolved: `CF-COMPAT` is deleted and determinant/conductor work is moved to `FLT-INDUCED-MOD` or `IND-CONDUCTOR`. |
| 5. Reciprocity direction | Not resolved. `Kˣ → W_Kᵃᵇ`, uniformizer ↦ geometric Frobenius is a coherent geometric normalization, but the repair calls it the “arithmetic Artin map.” More importantly, it never states the required derivation `I_K → W_Kᵃᵇ →[rec⁻¹] Kˣ`, proves its image lies in `𝒪_Kˣ`, then reduces to `k(v)ˣ`. The existing [`localTameAbelianInertiaGroup`](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:170) remains only an intended kernel with an explicit correctness TODO. |
| 6. Existing infrastructure | Only partially honest. The inertia and Galois-abelianization inventory is correct, but [`FiniteAdeleRing.unitEmbedding`](/Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean:176) cannot have its cokernel identified with the global topological idele-class object or its `π₀` without the archimedean and topology bridges. Mathlib explicitly warns that the idele topology is not inherited from the adele ring ([IsOpenUnits.lean](/Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/Topology/Algebra/IsOpenUnits.lean:22)). |
| 7. Exact T2-nameable interfaces | Partially resolved. The full reciprocity/globalization theorems are correctly non-nameable: `SRC-004` is explicitly incomplete ([SOURCE-REGISTER.md](/Volumes/second-store/devel/proof-forks/FLT/methodology/SOURCE-REGISTER.md:12)), and `[cf]` has no exact theorem/page locator, so the T2 assumption policy blocks them ([historical-assumptions.ndjson](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/historical-assumptions.ndjson:1)). The two `CF-CHAR` items are nameable only as kernel-clean definitions—not as sourced T2 assumptions. |

Read-only Lean test on Lean 4.32.0-rc1 / Mathlib `a3364fa`:

- The literal Stage-3 block fails because `𝓞` is not in scope.
- Adding `open NumberField` makes both exact definitions elaborate.
- Both then have axiom closure `[propext, Classical.choice, Quot.sound]`.
- This proves interface elaboration only; it proves no character existence, reciprocity, or globalization theorem.

Fable is **triggered** under the conditional ladder because the advertised exact first signature fails its literal elaboration gate. This is a failed signature/build condition, not an uncertainty verdict.

Next exact kernel unit: `FLTMethodology.Probes.ClassFieldCharacterBoundary`, containing only the two predicates, with:

```lean
import FLT.Deformations.RepresentationTheory.GaloisRep

open NumberField
```

followed by the repaired definitions and their `#print axioms` commands. Then build only:

```text
lake build FLTMethodology.Probes.ClassFieldCharacterBoundary
```

No repository files or control records were modified.
