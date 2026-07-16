# Current component inventory

Baseline inventory at frozen upstream commit `ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b`.

Live execution refresh at pre-checkpoint commit `0fa2249cb7abd649df86846eafcea1adfaadf631`:

- warm `FLT` and methodology builds passed;
- the monitor counted 27 executable verified-root admissions;
- the top axiom closure is `[knownin1980s, propext, sorryAx, Classical.choice, Quot.sound]`;
- after recording the operator-authorized review substitution and corrected graph, G0--G3 are
  green and G4--G6 remain open.

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
| Residual image/adequacy bridge | Required by the candidate lifting theorems | Absent; previously only risk prose | Explicit definition/source gap after Opus HR-02 |
| Automorphic form to Galois representation | Required before the localized `R → T` map | Absent as a source-compatible integrated construction | Explicit programme after Opus HR-03 |
| Auxiliary-field prime condition | Unramified in blueprint; split completely in the Taylor near-reference | Source choice unresolved | Explicit definition/source gap after Opus HR-04 |
| Potential-modularity assembly | Moret-Bailly, auxiliary curve, induced modularity, Jacquet–Langlands | Mostly absent as an integrated Lean route | Critical path |
| Automorphic-to-Galois compatible family | Blueprint nodes `compatible_family` and associated construction | Central definitions/theorems absent or exploratory | Critical path |
| Brauer--Nesbitt comparison | `FLTProbe.BrauerNesbitt.GroupContract` and its consumer bridges | Joint-image reduction, residual specialization, and residual rank transport are kernel-clean; reviewed narrowing is partial only and the terminal theorem remains absent | Coefficient and compatible-family prerequisite |
| Historical finite assumptions | `Mazur_statement`, `Odlyzko_statement`, local/global class field and related results | Some named axioms; many interfaces absent | T2 boundary; T3 proof work |
| Top theorem | `flt`, `PNat.pow_add_pow_ne_pow` | Compiles upstream but is not kernel-clean | T1–T3 terminal |

## Live W00 classification

The refreshed graph exposes three source-vocabulary prerequisites in addition to the original four
W00 gate nodes. Therefore the live denominator is seven; one refreshed node and one original core
node are now complete.

| Node | Classification | Immediate reason |
|---|---|---|
| `FLT-MLT-COEFFICIENTS` | ACTIVE | Four coefficient/residual relations and the exact Brauer--Nesbitt consumer boundary are signature-green; stable-lattice independence and the arbitrary-field Brauer--Nesbitt proof remain open |
| `FLT-MLT-PADIC-HODGE` | BLOCKED | Depends on the coefficient/lattice boundary |
| `FLT-RACAR-DEF` | BLOCKED | Depends on coefficient data and the admitted automorphic support cluster |
| `FLT-SGOOD-DEF` | COMPLETE | Exact four-field definition builds with the standard axiom trio and independent Fable/GPT reviews accept it |
| `FLT-MLT-SOURCE` | BLOCKED | Taylor 2018 is selected, but the three source-vocabulary nodes and exact Lean signature remain open |
| `FLT-SGOOD-SELECTED` | BLOCKED | Depends on the source contract and explicit finite-flat/p-adic-Hodge bridge |
| `FLT-AUX-LOCAL-FIELD` | BLOCKED | Depends on the source contract and absent Moret--Bailly specialization |

W00: `1 / 7` refreshed nodes complete (`1 / 4` original core nodes).

## Live W02 classification

| Node | Classification | Reachable live admission summary |
|---|---|---|
| `FLT-TATE-TORSION` | BLOCKED | Two admissions remain, and the file explicitly requires coordination with KB and David Angdinata before work on them |
| `FLT-TATE-FLAT` | BLOCKED | The resultant degree normalization is kernel-clean; the universal division-polynomial identity, easy Neron--Ogg--Shafarevich theorem, local/global torsion-action bridge, and finite-flat group-scheme/Hopf-algebra input at `P.p` remain |
| `FLT-TATE-UNRAMIFIED` | ACTIVE | Four Galois-action helpers, Tate-curve ellipticity, and the concrete/formal reciprocal-j bridge are kernel-clean; nine admissions remain, with the first construction leaf blocked on the integral Euler-product discriminant identity and local-field descent |
| `FLT-TATE-WEIL` | BLOCKED | The current pairing type admits the zero map, which fails the frozen Tate normalization consumer; a source-faithful Weil-pairing construction is absent |
| `FLT-SUPPORT-TATE` | BLOCKED | Join waits for all four support subclusters |
| `FLT-TORSION-001` | BLOCKED | `WeierstrassCurve.galoisRep` waits for `FLT-TATE-TORSION` closure |
| `FLT-FREY-HR` | BLOCKED | Two direct admissions and dependencies on torsion and the support join |

W02: `0 / 7` nodes complete. The exact missing good-reduction specialization contract is now
signature-green, but existing helpers do not close an aggregate node while an exported consumer
still has `sorryAx`.

## Status vocabulary

- **Verified and reusable:** declaration compiles and is suitable for the stated role; axiom closure
  still must be checked when it becomes load-bearing.
- **Admitted:** a declaration or data field is implemented with `sorry`.
- **Historical boundary:** a custom assumption deliberately exposed by T1/T2.
- **Definition gap:** the mathematical object required to state a later theorem is missing.
- **Absent:** neither an adequate statement nor proof exists at this frozen commit.
- **Exploratory:** source may be useful as a pattern but is not frozen critical-path infrastructure.
