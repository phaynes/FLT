# FLT component bill of materials

Task: `task:fg-flt-ra-component-bom-20260716`  
Frozen obligation baseline: 52 records in `methodology/control/proof-obligations.ndjson`  
Binding authority: `methodology/control/component-bom.ndjson`

## Contract

Every frozen proof obligation has exactly one implementation owner. Ownership does not mean that a
component may strengthen, weaken, or silently replace the obligation: its source references, exact
Lean declaration or proposed signature, dependency list, stage target, and completion gate remain
the records in `proof-obligations.ndjson`.

An edge between obligations owned by different components is a component interface. A component may
consume that interface only after the provider's exact declaration, source reconciliation, axiom
closure, and required review pass. Historical mathematics is never copied into a modern component;
it is consumed through the T1/T2/T3 adapters planned by FLT-206.

The provider-neutral `FreyContradictionInterface` is an integration component with no new frozen
mathematical obligation. It packages the final join but does not discharge any of the 52 nodes.

## Work-package inventory

The 25 owner work items below contain 31 independently named mathematical contract components. A
work item is a scheduling and review envelope, not a theorem interface. In particular, FLT-204 owns
separate root-vocabulary and terminal-adapter contracts; collapsing those into one graph node creates
a false scheduling cycle even though their mathematical contracts are ordered and acyclic.

| Work item | Component | Owned obligations | Boundary |
|---|---|---:|---|
| FLT-204 | existing verified adapters | 8 | Frozen definitions and already-clean boss endpoints |
| FLT-301 | Mazur | 1 | Named Frey irreducibility input |
| FLT-302 | cyclic base change | 1 | Base-change provider |
| FLT-303 | Moret--Bailly | 1 | Local-condition existence provider |
| FLT-304 | class field theory | 1 | Local/global reciprocity providers |
| FLT-305 | Jacquet--Langlands | 1 | Exact level/coefficient transfer |
| FLT-306 | induced modularity | 1 | Automorphy of induced representations |
| FLT-307 | Fontaine--Odlyzko | 1 | Exceptional residual classification |
| FLT-308 | Chebotarev | 1 | Trace comparison to representation equality |
| FLT-309 | Brauer--Nesbitt | 1 | Exact semisimple comparison contract |
| FLT-310 | quaternion boundary | 1 | Historical quaternionic specialization |
| FLT-401 | Tate--Frey | 7 | Torsion, Tate support, and concrete hardly ramified Frey input |
| FLT-402 | Galois deformation | 3 | Support, representability, and local balance |
| FLT-403 | Taylor--Wiles | 2 | Auxiliary primes and patching terminal |
| FLT-404 | MLT source contract | 2 | Selected source theorem and selected good condition |
| FLT-406 | coefficients | 1 | Lattices, residual reduction, and scalar transport |
| FLT-407 | p-adic Hodge | 1 | Finite-flat/crystalline and Hodge--Tate bridge |
| FLT-408 | automorphic/Galois | 3 | RACAR vocabulary, support, and attached representations |
| FLT-409 | potential modularity terminal | 1 | Assembly over auxiliary construction and MLT |
| FLT-410 | compatible family | 3 | Lift, Brauer descent, and family membership |
| FLT-411 | terminal reducibility | 4 | Mod-3, three-adic, comparison contradiction, and generic endpoint |
| FLT-412 | concrete Frey adapter | 2 | Exact B4/B3 join into the clean contradiction interface |
| FLT-413 | auxiliary/residual image | 3 | Auxiliary field/curve and residual-image output |
| FLT-414 | Hecke action | 1 | Localized module, attached representation, and surjective R-to-T map |
| FLT-415 | MLT terminal | 1 | Final selected modularity-lifting consequence |
| **Total** |  | **52** | 42 T1-target and 10 T2-first obligations |

FLT-405 is intentionally absent. Ribet's theorem is not a separate obligation on the selected
architecture: the terminal non-irreducibility result is owned by FLT-411 and its binding to the
concrete Frey representation by FLT-412. Creating a second Ribet owner would duplicate the final
contract.

## Join order

The mathematical dependency order, after the architecture/source gates, is:

1. existing clean vocabulary and the ten exact historical interfaces;
2. Tate--Frey, coefficients, p-adic Hodge, automorphic/Galois, and deformation foundations;
3. the MLT source contract, auxiliary/residual-image construction, and Hecke action;
4. Taylor--Wiles patching and the modularity-lifting terminal;
5. potential modularity, compatible families, and terminal reducibility;
6. the concrete Frey adapter and provider-neutral boss integration;
7. the exact closed public theorem and T1/T2/T3 assurance audits.

This is a partial order, not permission to prove downstream claims early. Within a component, each
mapped obligation remains a separate subgate; an aggregate build cannot hide an open member.

## Minimality decisions

- Existing kernel-clean declarations are adapted, not copied into new theorem families.
- Historical providers are split because their sources and eventual unconditional proofs change
  independently.
- Coefficients, p-adic Hodge theory, automorphic attachment, Hecke localization, and patching remain
  separate: their data flow joins, but their proof technologies and falsifiable contracts differ.
- Potential modularity, compatible-family construction, and terminal reducibility remain separate
  serialized terminals; combining them would recreate the present long assurance tail.
- The final abstract contradiction interface owns no deep fact. Concrete semantics are checked only
  at FLT-412, where both the proposition definitions and axiom closure are auditable.

## Deterministic acceptance checks

The BOM is accepted only if all of the following are mechanically true:

1. both NDJSON files have 52 valid records;
2. obligation IDs are unique in each file and the two ID sets are equal;
3. every BOM binding has `coverage = "exact"` and a known owner work item;
4. every obligation retains at least one source reference;
5. the obligation graph and its 31-node projection by the BOM `component` field are acyclic;
6. no owner is empty except the explicitly non-owning integration interface;
7. FLT-405 owns no obligation and no obligation has two owners.

Passing this gate freezes ownership, not mathematical signatures. FLT-205 must still reconcile every
source, hypothesis translation, sublemma graph, library match, and elaborating signature before the
corresponding provider is ready for proof construction.

Projecting by `owner_work_item` is explicitly invalid: a tracked work package may hold several
ordered contracts. The initial audit deliberately tried that coarser projection and found cycles
through FLT-204, because its root definitions and final endpoint adapters were conflated. Projecting
the exact `component` field eliminates that false conflation. This distinction is a required input to
the later Rust programme controller.
