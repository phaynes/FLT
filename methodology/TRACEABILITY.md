# FLT proof-program traceability

This document is a human index over the machine-readable graph in
`control/proof-obligations.ndjson`. The generator derives every edge from the node's declared
dependencies and fails if the current graph contains a cycle. At this design revision the graph
contains 52 obligations, 95 direct edges, 52 critical-path obligations, and no cycle. Each strongly
connected component is therefore a singleton and is recorded explicitly by `scc_id`.

The high number of critical nodes does not imply uniform effort: estimates range from already
proved composition terms to research programmes with unbounded upper-tail risk.

## Terminal trace

```text
PNat.pow_add_pow_ne_pow                                      FLT-TOP
  <- flt                                                    FLT-B1
    <- B2_proof                                             FLT-B2
      <- B3_proof                                           FLT-B3
        <- B4_proof                                         FLT-B4
          <- Frey p-torsion hardly ramified                 FLT-FREY-HR
          <- generic hardly-ramified reducibility           FLT-HR-REDUCIBLE
             <- characteristic-zero lift                    FLT-LIFT
             <- compatible-family terminal contradiction    FLT-COMPAT-CONTRA
```

`FLT-B3` also consumes the Mazur irreducibility input. That is permitted as a visible
`knownin1980s` dependency only at T1; T2 replaces the generic authority with a finite sourced
interface, and T3 proves it.

## Post-1989 central route

The residual reducibility argument has four large joins:

1. exact S-good deformation conditions and representability;
2. potential modularity, including Moret-Bailly, class field theory, induced modularity,
   Jacquet-Langlands, and the selected modularity-lifting theorem;
3. characteristic-zero lift and compatible-family construction via Brauer induction;
4. mod-3 and 3-adic classification followed by Chebotarev/Brauer-Nesbitt comparison.

The modularity-lifting route is selected but not statement-frozen in Lean. Taylor 2018, Theorem
2.1.1 is the governing source theorem. Its witness-unramifiedness hypothesis is local at places
`v | ell`, and its conclusion is level-free GL2 automorphy. `FLT-MLT-COEFFICIENTS`,
`FLT-MLT-PADIC-HODGE`, and `FLT-RACAR-DEF` expose the missing source vocabulary before
`FLT-MLT-SOURCE`. `FLT-SGOOD-DEF` is now a reviewed kernel-clean encoding of the blueprint's
temporary four-field target, while
`FLT-SGOOD-SELECTED` is a separate repository-local bundle whose bridge to the source theorem must
be proved. No scaffold may identify either source boundary with `IsAutomorphicOfLevel S`.

The reviewed graph also exposes three previously implicit programmes: the residual-image or
adequacy bridge (`FLT-RESIDUAL-IMAGE`), the automorphic-form-to-Galois construction
(`FLT-AUT-GALOIS`), and the source-selected auxiliary-field local condition
(`FLT-AUX-LOCAL-FIELD`). The Tate support umbrella is decomposed into torsion, finite-flat,
Tate-curve, and Weil-pairing subclusters before scheduling.

## Target trace

| Target | Terminal gate | Allowed custom boundary | Required closure |
|---|---|---|---|
| T1 | G4 | `knownin1980s` only, visible in the top audit | No `sorryAx` |
| T2 | G5 | Finite, named, exactly typed historical assumptions | No generic `knownin1980s` |
| T3 | G6 | None | `[propext, Classical.choice, Quot.sound]` |

## Source-to-node trace

| Source area | Principal nodes | Current risk |
|---|---|---|
| First reductions and Frey curve | `FLT-DEF-001`, `FLT-TATE-*`, `FLT-TORSION-001`, `FLT-FREY-HR`, `FLT-B4` | Existing admitted data and ramification proof |
| Hardly-ramified blueprint | `FLT-LIFT`, `FLT-FAMILY`, `FLT-MOD3`, `FLT-THREEADIC`, `FLT-COMPAT-CONTRA` | Four admitted terminals plus absent composition |
| Potential modularity | `FLT-MORET-BAILLY`, `FLT-AUX-CURVE`, `FLT-INDUCED-MOD`, `FLT-JL`, `FLT-POTMOD` | Mostly prose or absent interfaces |
| Modularity lifting | `FLT-MLT-COEFFICIENTS`, `FLT-MLT-PADIC-HODGE`, `FLT-RACAR-DEF`, `FLT-SGOOD-DEF`, `FLT-MLT-SOURCE`, `FLT-SGOOD-SELECTED`, `FLT-RESIDUAL-IMAGE`, `FLT-AUT-GALOIS` through `FLT-MLT` | Taylor 2018 selected; source vocabulary and repository-level bridges remain absent |
| Compatible families | `FLT-COMPAT-DEF`, `FLT-BRAUER-FAMILY`, `FLT-CHEBOTAREV`, `FLT-BRAUER-NESBITT` | The FLT-scoped rank-two Brauer--Nesbitt theorem and direct coefficient consumer are proved and independently reviewed. Compatible-family construction and the Chebotarev passage from almost-all Frobenius data to all elements remain open. |
| Historical boundary | `FLT-HIST-MAZUR`, `FLT-HIST-QUATERNION`, `FLT-FONTAINE-ODLYZKO`, `FLT-CBASE`, `FLT-JL` | T1/T2/T3 treatment differs and must remain explicit |

## State meanings

- `proved` means the declaration is present and elaborates; its downstream axiom closure may still
  be red.
- `admitted` means an existing declaration or load-bearing data object uses `sorry`.
- `absent` means no adequate integrated declaration is present.
- `definition-gap` means prerequisite objects are not yet sufficient to freeze an honest theorem
  signature.
- `historical-assumption` means an explicit T1/T2 boundary, never an unconditional proof.

The generator, schema, scaffold probes, independent reviews, and monitor provide distinct gates.
Passing one does not imply any other.

`target_stage` records the first stage at which an obligation becomes explicit.
`completion_targets` records every terminal closure in which it remains load-bearing. In particular,
the T2 historical-interface nodes also list T3, and their `stage_completion` requires a
standard-axiom proof at T3. This represents T3 proof work without pretending that a second, weaker
mathematical declaration discharges the same proposition.
