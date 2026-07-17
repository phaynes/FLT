# Stage 4 Opus 4.8 post-diversity synthesis — coefficients

## Verdict: READY-FOR-GPT-REVIEW

This synthesis preserves the GPT refutation of the original coefficient design, independently
checks the Fable repair against the pinned APIs, and freezes one source- and Lean-exact interface
plan. It was read-only and did not register an axiom or promote an obligation.

## Preserved corrections

- The generic representation carries the real hypothesis `Module.rank E V = 2`; no theorem is
  quantified over arbitrary-rank `V` while demanding a rank-two lattice.
- `(O : Type*)` is explicit choice data. Making it implicit leaves `Nonempty
  (StableLatticeData ...)` uninferable.
- The full coefficient, topology, fraction-field, scalar-tower, and residual context appears in
  declaration headers instead of erasable section variables.
- Residual comparison includes explicit embeddings into `AlgebraicClosure (ZMod p)`.
- Genuine lattice independence compares residual models from two different integral models of the
  same generic representation. The same-`rho0` relation remains a distinct weaker statement.
- Brauer–Nesbitt and scalar-extension semisimplicity enter only as named hypotheses, never axioms.

The repaired compatibility chain

```lean
(rho0.baseChange E).conj r0 = rho
```

matches the real `GaloisRep.baseChange` and `GaloisRep.conj` APIs.

## Frozen interface units

1. `StableLatticeData p hp O hV rho`
   stores a finite free rank-two integral module `V0`, `rho0 : GaloisRep F O V0`, a generic-fibre
   equivalence `r0 : E ⊗[O] V0 ≃ₗ[E] V`, and the compatibility equation above.
2. `CoefficientData p hp O hV rho`
   adds a finite free residual module, a residual `GaloisRep`, and
   `IsSemisimplifiedResidualModel rho0 rhoBar`. The flat form is retained for the production probe;
   an `extends StableLatticeData` form is only an ergonomic candidate.
3. `AgreeInResidualClosure`
   specializes `ResidualModelsAgreeAfterExtension` to `AlgebraicClosure (ZMod p)` with both
   residue-field embeddings and continuous scalar actions explicit.
4. `LatticeIndependent`
   states semisimple residual equivalence for two coefficient bundles of the same `rho`.
5. `latticeIndependent_of_groupContract`
   conditionally discharges the same-residue-field comparison from the exact Brauer–Nesbitt
   `GroupContract.{uO, uF, 0, 0}` hypothesis.
6. Supporting wiring:
   `charpoly_baseChange_eq_of_generic` and
   `residual_charpoly_eq_of_two_integral_models`.

## Dependency split

Bankable definitions and conditional wiring remain separate from:

- T-A1: existence of stable lattices for continuous rank-two representations;
- T-A2: Noetherianity, finite residue field, and adic completeness from the minimal coefficient
  hypotheses;
- T-A3: existence of semisimplified residual models;
- M4: ascent of semisimplicity to the residual algebraic closure;
- BN: the exact Brauer–Nesbitt theorem contract;
- T-IND-CLOSURE: cross-coefficient-ring residual comparison.

Any statement consuming one of these takes it as an explicit hypothesis until the corresponding
node is discharged.

## Corrected consumer ledger

The earlier claim that p-adic-Hodge, RACAR, and SelectedGood were current compiled consumers was
false: those declarations do not yet exist in `FLT/`. The actual live consumers are:

- `GaloisRep.IsAutomorphicOfLevel`, which uses the generic coefficient side;
- `GaloisRepresentation.IsHardlyRamified.lifts`, whose exact base-change/conjugacy boundary forces
  finite discrete residual coefficients;
- `Deformation.ProartinianCat.self` and representability code, which require a complete Noetherian
  local coefficient ring with finite residue field and therefore consume T-A2.

`DiscreteTopology (ResidueField O)` is thus a real consumer requirement. The generic
`AlgebraicClosure ℚ_[p]` embedding binders from the earlier draft are dropped from the data structure
because only the residual closure is used there.

## Smallest production slice

Create `FLTMethodology/Probes/MLTCoefficientData.lean` containing the four definitions, existence
predicates, M4 contract, the two characteristic-polynomial lemmas, and conditional lattice
independence, then register it in `FLTMethodology.lean`.

The first expected non-mechanical goal is to descend equality of generic-fibre characteristic
polynomials through `IsFractionRing` injectivity to equality over `Polynomial O`, then reapply
residual base change. The required pinned lemma is `LinearMap.charpoly_baseChange`, or an equivalent
reconstruction through matrices.

Acceptance requires the targeted build and every declaration's `#print axioms` to return exactly
`[propext, Classical.choice, Quot.sound]`.

## Fresh-review questions

1. Keep the source-faithful `IsDiscreteValuationRing O` contract, or relax to the weaker live
   consumer requirements?
2. Retain the confirmed flat `CoefficientData`, or adopt the unconfirmed `extends` packaging?
3. Does the production signature reproduce the temporary proofs without hidden topology/universe
   assumptions?

Stable-lattice existence, coefficient glue, semisimplification existence, semisimplicity ascent, and
Brauer–Nesbitt remain explicitly open mathematical nodes. This design does not claim otherwise.
