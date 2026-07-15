# FLT proof-program traceability

This document is a human index over the machine-readable graph in
`control/proof-obligations.ndjson`. The generator derives every edge from the node's declared
dependencies and fails if the current graph contains a cycle. At this design revision the graph
contains 49 obligations, 77 direct edges, 48 critical-path obligations, and no cycle. Each strongly
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

The modularity-lifting branch is not statement-frozen. `FLT-SGOOD-DEF` now records only the
blueprint's temporary four-clause target. `FLT-MLT-SOURCE` records the explicit source mismatch,
and `FLT-SGOOD-SELECTED` is downstream of source selection. This breaks the design cycle found in
review: neither a scaffold nor implementation may invent a final local condition before selecting
an exact theorem.

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
| Modularity lifting | `FLT-SGOOD-DEF`, `FLT-MLT-SOURCE`, `FLT-SGOOD-SELECTED`, `FLT-RESIDUAL-IMAGE`, `FLT-AUT-GALOIS` through `FLT-MLT` | Exact primary theorem unresolved; large missing programmes |
| Compatible families | `FLT-COMPAT-DEF`, `FLT-BRAUER-FAMILY`, `FLT-CHEBOTAREV`, `FLT-BRAUER-NESBITT` | Definition present, construction and terminal comparison absent |
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
