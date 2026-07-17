# Stage 5 independent review — GPT-5.6 xhigh

## Verdict: `REVISE-SUBSTANTIVE`

The five-unit repository boundary is mechanically correct, but the gated source synthesis still has
substantive statement and dependency defects.

## Blocking findings

1. **H4 uses the wrong irreducibility predicate.** The target states ordinary
   `GaloisRep.IsIrreducible` on `coeff.rhoBar` after restriction to `CyclotomicField`. Because
   `rhoBar` is over a finite residue field, this is weaker than irreducibility after extension to an
   algebraic closure. It must use absolute irreducibility, or extend the same selected model to the
   common residual algebraic closure first. A two-dimensional `C₃` representation over `𝔽₂` with
   minimal polynomial `x²+x+1` is irreducible over `𝔽₂` but splits over `𝔽₄`, so ordinary
   irreducibility cannot silently stand for absolute irreducibility.

2. **The weight owner is disconnected from the actual representation.** `regular` and
   `fontaineLaffaille` constrain a free `weights : AbstractWeightData`, while `weightsMatch`
   separately refers to `htWeights r ι`. No equality connects `weights` to `htWeights r ι`.
   Repair by defining the constraints directly on extracted weights or adding an explicit equality
   owned by the Tier-2 extraction/transport boundary.

3. **Residual agreement is not coefficient-exact.** The synthesis uses same-field
   `SemisimpleResidualEquivalent coeff.rhoBar (attachedResidual …)`. The coefficient review instead
   requires explicit embeddings into a common residual closure. Unless the RACAR residual is proved
   to use the identical residue field, H2 must use the reviewed closure-comparison boundary.

4. **The dependency ledger is inconsistent and partly reversed.** The synthesis says
   `FLT-MLT-SOURCE` consumes `FLT-RESIDUAL-IMAGE`, while the live graph makes
   `FLT-RESIDUAL-IMAGE` depend on `FLT-MLT-SOURCE`. Introduce a neutral absolute-residual-predicate
   vocabulary upstream of the source contract; concrete residual-image proofs should discharge it
   later at the application/potential-modularity layer.

## Temporary Lean results

The exact Stage-4 five-unit probe was streamed to Lean. All declarations elaborated with the proposed
imports, namespace, universes, and typeclasses, each with exactly
`[propext, Classical.choice, Quot.sound]`:

- `SelectedGoodRepository`;
- `HasGenericTameRankOneQuotient`;
- `HasFlatDescentAboveEll`;
- `CyclotomicDegreeBound`;
- `ComplexEmbeddingData`.

The exact consumer application to `cyclic_base_change` also elaborated and produced the live
`IsAutomorphicOfLevel` equivalence. The five declarations do not term-depend on that theorem:

```text
IsAutomorphicOfLevel: [propext, Classical.choice, Quot.sound]
cyclic_base_change:   [propext, sorryAx, Classical.choice, Quot.sound]
```

The nine-declaration p-adic-Hodge Tier-1 probe also re-elaborated with the standard trio. Its
`{-1,0}` convention at repository `ρ` and `{0,1}` at `GaloisRepDual ρ` is correct.

## Accepted separation and disposition

The synthesis correctly preserves generic-fibre tame quotient, integral flat descent, and
`BlueprintSGood.traceOnJ` as distinct; support away from `ell`; the cyclotomic-degree argument;
at-`ell` RACAR unramifiedness versus away-from-`ell` automorphy; level-free source automorphy versus
the derived repository theorem; and gating on coefficients, p-adic-Hodge Tier-2, and RACAR.

Those correct separations do not repair the four defects above. No build is authorized under this
verdict. The bounded five-unit probe is technically green but remains unpersisted because the gate
requires PASS.

The first expected residual after repairing H4 is transport of
`Representation.IsAbsolutelyIrreducible` across the chosen residual coefficient extension and
action-range equivalence, likely via an order isomorphism between the corresponding
`Subrepresentation` lattices.
