# Independent adjudication: FLT-scoped Brauer–Nesbitt graph promotion

Review commit `0b4b3a8` read-only against parent `dfb9694`. Do not edit.

The change narrows the programme obligation `FLT-BRAUER-NESBITT` from the
unneeded general-dimensional textbook contract to the exact rank-two theorem
used by FLT representations, records it as `proved` / `proof-green`, and keeps
`FLT-CHEBOTAREV` separately absent. This is a control and scope adjudication,
not a request to re-review the Lean proof already independently passed.

Hostile checks:

1. Inspect every actual or graph-declared consumer of `FLT-BRAUER-NESBITT`.
   Is each intended representation genuinely rank two, or does any live
   consumer require the general-dimensional `Contract`?
2. Does the direct coefficient/lattice consumer really remove its abstract
   Brauer–Nesbitt premise? Does any other implemented consumer remain unwired?
3. Is it honest to keep Chebotarev open for the almost-all-Frobenius to
   all-elements passage, rather than laundering that premise through the
   Brauer–Nesbitt green state?
4. Are the source gap, Fable execution limitation, bounded theorem scope, and
   standard-trio evidence represented accurately and consistently across the
   canonical NDJSON, generated graph/instances, source-design register, source
   packet, traceability, source register, and component inventory?
5. Re-run `methodology/control/generate_graph.py`, the structural `jq` checks,
   and `lake build FLT FLTMethodology` if the read-only environment permits.
   Identify any generated-file drift or schema/state mismatch caused by this
   change. Do not attribute pre-existing schema drift to this commit without
   proving it is new.

Return exactly one verdict, `PASS` or `REVISE`, then numbered findings with
file and line references. `PASS` means only that the FLT-scoped rank-two
milestone is correctly promoted and its remaining dependency boundaries are
honest. It must not imply completion of the general-dimensional contract,
Chebotarev, the other coefficient providers, a compatible-family terminal, or
FLT.
