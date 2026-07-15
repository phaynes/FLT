# Library and proof-matching survey

The survey targets the frozen FLT repository and its pinned Mathlib revision. Candidates are ranked
by signature and graph position, not by theorem-name resemblance. `#check` probes live in
`FLTMethodology/Probes/LibraryMatches.lean`; an elaborating probe establishes presence and type only.

## Highest-value candidates

| Candidate | Match | Value | Limitation |
|---|---|---|---|
| `FermatLastTheorem.of_p_ge_5` | Exact | Closes B2→B1 | Downstream only |
| `PNat.pow_add_pow_ne_pow_of_FermatLastTheorem` | Exact | Closes public terminal bridge | Downstream only |
| `FLT.Bosses.B4_implies_B3` | Exact | Frozen B4→B3 reduction | Keeps Mazur boundary |
| `GaloisRep.baseChange` | Adaptable | Required by lift/family identifications | No existence theorem |
| `GaloisRepFamily.isCompatible` | Exact definition | Candidate family interface | Terminal sufficiency unreviewed |
| `Deformation.SLiftFunctor` | Adaptable | Very close to the four S-good conditions | Exact local/source match open |
| `Deformation.narrowSLiftFunctor` | Adaptable | Stronger trace variant already encoded | May be the wrong local condition |
| `narrowSLiftUniversalRingCorepresentableBy` | Pattern | Desired universal-ring shape | Depends on an admitted theorem |
| `ker_RtoT_le_nilradical` | Adaptable | Substantial kernel-clean patching terminal | Gives nilradical containment under many hypotheses |
| `GaloisRep.IsAutomorphicOfLevel` | Exact definition | Frozen project automorphy notion | Surrounding analytic construction incomplete |
| `cyclic_base_change` | Signature only | Exact thematic base-change interface | Proof admitted; image/descent theorem may still be missing |
| `GaloisRepresentation.IsHardlyRamified` | Exact definition | B5/B6 common interface | Source-field reconciliation still required |

## Consequential missing interfaces

The searches did not locate exact reusable declarations for: the selected modularity-lifting source
contract; balanced local finite-flat deformation conditions; Taylor-Wiles prime selection; the
localized Hecke/Galois R-to-T action; Moret-Bailly with the required disjointness; the selected
Jacquet-Langlands transfer; induced residual automorphy; Brauer compatible-family construction;
Chebotarev comparison; Brauer-Nesbitt in the required coefficient setting; or the complete
Fontaine-Odlyzko mod-3 classification.

These are missing interfaces, not claims that no relevant mathematics or partial library support
exists. Every one must be re-searched after an exact statement is frozen, since normalization and
typeclass choices materially affect reuse.

## False-positive controls

- A name match is rejected when the conclusion orientation, local conditions, coefficient type, or
  source hypotheses do not unify.
- An admitted declaration is classified `signature-only` or `admission-dependent`, never exact
  proof reuse.
- The generic patching theorem is not called an FLT modularity-lifting theorem.
- Current Mathlib outside the pinned revision may inform a future migration decision but is not a
  dependency of this frozen experiment.
