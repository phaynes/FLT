# Opus 4.8 hostile mathematical review

Design commit: `5ddc1e6`

Model: `claude-opus-4-8`

The first broad invocation timed out without a verdict. A bounded source-critical retry completed
successfully in read-only mode. The bridge trace identified the exact configured model above.

## Verdict

**REVISE**

The reviewer independently confirmed 41 nodes, 58 edges, 40 critical-path nodes, an acyclic graph,
and no dangling dependencies. It found no false completion claim, but rejected freezing the
modularity-lifting, potential-modularity, and compatible-family subgraph before the following
repairs.

## Blockers

None classified by the reviewer. The first proof wave was judged safe only if restricted to
already-elaborating boss-chain and definition work; the central research route was not safe to
freeze.

## Major findings

### HR-01 — Source selection and S-good definition form a concealed design cycle

- Nodes: `FLT-MLT-SOURCE`, `FLT-SGOOD-DEF`.
- Evidence: `FLT-MLT-SOURCE` depends on `FLT-SGOOD-DEF`, while the source audit says the final
  S-good signature cannot be frozen until an exact modularity-lifting source is selected.
- Repair: split the blueprint-temporary local condition from the source-selected final condition,
  or represent and review the strongly connected component explicitly.
- Confidence: high. Primary-source or kernel evidence required: no.

### HR-02 — Residual image/adequacy is not a standalone obligation

- Nodes: `FLT-MLT-SOURCE`, `FLT-MLT`, `FLT-TW-PRIMES`, `FLT-POTMOD`.
- Evidence: the blueprint requires absolute irreducibility after restriction to the cyclotomic
  extension; the near-reference conditions range from that condition to an image containing
  `SL₂(F_p)`. The graph only mentions the issue in risk prose.
- Repair: add an explicit, sourced obligation establishing the selected residual-image condition
  for every representation entering modularity lifting and Taylor-Wiles prime selection.
- Confidence: high. Primary source required: yes.

### HR-03 — Automorphic-form-to-Galois construction is hidden inside an umbrella cluster

- Nodes: `FLT-HECKE-ACTION`, `FLT-SUPPORT-AUTOMORPHIC`.
- Evidence: existence and local-global compatibility of the attached Galois representation are
  only a risk-line item, although they are a programme needed before the `R → T` map is meaningful.
- Repair: promote the construction to its own sourced node feeding the Hecke-action/R-to-T work.
- Confidence: high. Primary source required: yes.

### HR-04 — Taylor's split-completely auxiliary-field condition is implicit

- Nodes: `FLT-AUX-CURVE`, `FLT-MORET-BAILLY`, `FLT-MLT-SOURCE`.
- Evidence: the blueprint asks only for the residual prime to be unramified, whereas Taylor's
  near-reference requires it to split completely. The auxiliary-field nodes currently state only
  the weaker condition.
- Repair: if Taylor is selected, make splitting part of the Moret-Bailly local conditions; if Gee
  is selected, pursue its stronger residual-image condition instead. Do not leave both routes
  latent in one contract.
- Confidence: medium. Primary source required: yes.

## Minor findings

### HR-05 — Generic reducibility scaffold is stronger than the blueprint route

- Node: `FLT-HR-REDUCIBLE`.
- Evidence: the scaffold assumes only an odd residual prime, admitting `ell = 3`, while the intended
  generic endpoint begins at `ell ≥ 5`; the mod-3 case belongs to a separate branch.
- Repair: add `5 ≤ ell` to the scaffold endpoint.
- Confidence: high. Kernel probe required after repair.

## Notes

- `proved` in the graph currently means that a declaration elaborates, not that its transitive
  axiom closure is clean. External reports must keep that distinction explicit.
- The four-admission methodology scaffold was judged honest and outside the verified FLT root.
- The blueprint's informal “well-known to experts” bridge is not an acceptable authority; the
  source register correctly refuses to rely on it.
- The `FLT-SUPPORT-TATE`, `FLT-SUPPORT-AUTOMORPHIC`, and `FLT-SUPPORT-DEFORMATION` umbrella nodes
  must be decomposed before their proof waves.

## Dependency-ordered repair list

1. Split the temporary and final S-good definitions.
2. Select and source the modularity-lifting route, including split-versus-unramified behaviour.
3. Add the residual-image/adequacy obligation.
4. Add the automorphic-to-Galois construction and compatibility obligation.
5. Decompose the Tate support cluster before Frey-ramification work.
6. Restrict the generic reducibility scaffold to residual primes at least five.
