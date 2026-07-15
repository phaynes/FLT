# Current component inventory

Inventory at frozen upstream commit `ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b`.

The source scan finds 59 executable-looking `sorry` sites under the verified module root, plus two
direct tactic uses of `knownin1980s`. This count is supplementary: comments, admitted data, and
absent mathematics make raw source counts unsuitable as completion percentages. Lean axiom and
transitive-sorry audits are the authority for individual declarations.

| Component | Representative declarations | State | Critical-path role |
|---|---|---|---|
| Elementary FLT reduction | `FLT.Bosses.B1`–`B3`, `B2_implies_B1`, `B3_implies_B2` | Verified and reusable | T1–T3 |
| Frey package and curve | `FreyPackage`, `FreyPackage.freyCurve` | Verified and reusable | T1–T3 |
| Elliptic-curve torsion/Galois representation construction | `WeierstrassCurve.galoisRep` and torsion support | Admitted data and theorems | T1–T3 definition/proof gap |
| Mazur irreducibility bridge | `FreyPackage.mazur` | Deliberate generic `knownin1980s` boundary | T1 permits the boundary; T2/T3 replace it |
| Current boss endpoint | `FLT.Bosses.B4_proof` | Admitted | Direct top-closure blocker |
| Hardly-ramified predicate | `GaloisRepresentation.IsHardlyRamified` | Verified definition | T1–T3 |
| Frey ramification | `FreyCurve.torsion_isHardlyRamified` | Statement contains admitted rank evidence; proof admitted | T1–T3 |
| Generic hardly-ramified reducibility | Intended `FreyCurve.torsion_not_isIrreducible` route | Export admitted; generic composition theorem absent | T1–T3 |
| Characteristic-zero lift | `GaloisRepresentation.IsHardlyRamified.lifts` | Admitted | Post-1989 critical path |
| Compatible family | `GaloisRepresentation.IsHardlyRamified.mem_isCompatible` | Admitted | Post-1989 critical path |
| Mod-3 classification | `GaloisRepresentation.IsHardlyRamified.mod_three` | Admitted | Mixed historical/current critical path |
| 3-adic trace/classification | `GaloisRepresentation.IsHardlyRamified.three_adic` | Admitted | Critical path |
| Automorphic representation predicate | `GaloisRep.IsAutomorphicOfLevel` | Verified definition | Modularity-lifting prerequisite |
| Cyclic base change | `cyclic_base_change` | Admitted | Potential-modularity prerequisite; historical boundary candidate |
| Deformation functors | `Deformation.SLiftFunctor`, `narrowSLiftFunctor` | Definitions present; corepresentability admitted | Modularity-lifting prerequisite |
| Generic patching algebra | `ker_RtoT_le_nilradical` and surrounding patching modules | Substantial verified infrastructure | Adaptable reuse, not yet an FLT modularity theorem |
| Quaternionic automorphic forms and Hecke operators | `HeckeAlgebra` and related modules | Substantial verified infrastructure with isolated admissions | Modularity-lifting prerequisite |
| Exact modularity-lifting theorem | Blueprint node `modularity_lifting_theorem` | Absent; current source says far from statement | Load-bearing statement/source blocker |
| Potential-modularity assembly | Moret-Bailly, auxiliary curve, induced modularity, Jacquet–Langlands | Mostly absent as an integrated Lean route | Critical path |
| Automorphic-to-Galois compatible family | Blueprint nodes `compatible_family` and associated construction | Central definitions/theorems absent or exploratory | Critical path |
| Historical finite assumptions | `Mazur_statement`, `Odlyzko_statement`, local/global class field and related results | Some named axioms; many interfaces absent | T2 boundary; T3 proof work |
| Top theorem | `flt`, `PNat.pow_add_pow_ne_pow` | Compiles upstream but is not kernel-clean | T1–T3 terminal |

## Status vocabulary

- **Verified and reusable:** declaration compiles and is suitable for the stated role; axiom closure
  still must be checked when it becomes load-bearing.
- **Admitted:** a declaration or data field is implemented with `sorry`.
- **Historical boundary:** a custom assumption deliberately exposed by T1/T2.
- **Definition gap:** the mathematical object required to state a later theorem is missing.
- **Absent:** neither an adequate statement nor proof exists at this frozen commit.
- **Exploratory:** source may be useful as a pattern but is not frozen critical-path infrastructure.
