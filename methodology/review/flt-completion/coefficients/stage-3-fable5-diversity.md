# Independent Fable 5 diversity design — coefficients

**Component:** `FLT-MLT-COEFFICIENTS`  
**Mode:** read-only, difficulty 10  
**Verdict:** `DESIGN-VIABLE`

All Lean checks were run through temporary files against Lean `4.32.0-rc1` and Mathlib
`a3364faec42918fcd84a03a255b50570129f9ead`. No repository file, task state, obligation, or axiom
was changed by the reviewer.

## Findings beyond the previous two stages

### The lattice-independence gap is smaller than previously claimed

The review produced a kernel-clean conditional route:

- `residual_charpoly_eq_of_two_integral_models` is provable unconditionally: semisimplified
  residual models attached to any two stable integral models of the same generic `rho` have equal
  characteristic polynomials on every Galois element.
- `latticeIndependent_of_groupContract` and its bundle-level form prove genuine two-lattice
  semisimple equivalence when the existing Brauer–Nesbitt `GroupContract` is supplied as an explicit
  hypothesis. The contract is not installed as an axiom.
- `AgreeInResidualClosure` elaborates over the fixed closure `AlgebraicClosure (ZMod p)` with
  explicit embeddings from both residue fields. Those embeddings cannot honestly be hidden or
  treated as canonical.

All these declarations audited to `[propext, Classical.choice, Quot.sound]` in temporary probes.

### The coefficient ring must be explicit

Lean drops section variables that are not used by structure fields. More subtly, an implicit
`{O : Type*}` makes `Nonempty (CoefficientData ...)` unelaborable because `O` occurs only in instance
binders and cannot be inferred from `rho`. The coefficient ring is choice data, so every repaired
signature takes `(O : Type*)` explicitly.

### Existing consumers fix the residual topology

`FLT/GaloisRepresentation/HardlyRamified/Lift.lean` requires finite discrete residual coefficients,
while `Deformation.ProartinianCat.self` requires a Noetherian, adically complete local coefficient
ring with finite residue field. The repaired context therefore includes
`DiscreteTopology (IsLocalRing.ResidueField O)`. The coefficient-glue theorem is not optional.

### Semisimplification is genuine missing mathematics

The pinned Mathlib provides only a semisimplicity predicate and elementary equivalences; it does not
construct semisimplifications. Existence remains an explicit T1 theorem obligation.

## Repaired interface context

Every unit retains the full explicit source context:

```lean
(p : ℕ) [Fact p.Prime] (hp : 2 < p)
(O : Type*)
{F E V : Type*}
[Field F] [NumberField F]
[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
[Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] [Module.Free ℤ_[p] O]
[TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[p] O]
[IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]
[IsAdicComplete (IsLocalRing.maximalIdeal O) O]
[Field E] [Algebra O E] [IsFractionRing O E]
[TopologicalSpace E] [IsTopologicalRing E] [Algebra ℤ_[p] E]
[IsScalarTower ℤ_[p] O E] [ContinuousSMul O E]
[Algebra E (AlgebraicClosure ℚ_[p])]
[ContinuousSMul E (AlgebraicClosure ℚ_[p])]
[TopologicalSpace (IsLocalRing.ResidueField O)]
[IsTopologicalRing (IsLocalRing.ResidueField O)]
[DiscreteTopology (IsLocalRing.ResidueField O)]
[ContinuousSMul O (IsLocalRing.ResidueField O)]
[AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
(hV : Module.rank E V = 2) (rho : GaloisRep F E V)
```

`IsNoetherianRing`, finiteness of the residue field, and adic completeness are demanded by the data
bundle; a separate glue theorem must derive them from the intended minimal DVR/finite-extension
hypotheses. They are not silently claimed as structure fields.

## Verified unit inventory

| Unit | Exact role | Status |
|---|---|---|
| U1 `StableLatticeData p hp O hV rho` | Integral module, rank two, integral representation, generic-fibre equivalence, conjugacy compatibility | elaborates; trio |
| U2 `CoefficientData p hp O hV rho` | U1 plus finite free residual module, residual representation, and `IsSemisimplifiedResidualModel` | elaborates; trio |
| U3 `AgreeInResidualClosure` | Comparison after explicit embeddings into `AlgebraicClosure (ZMod p)` | elaborates; trio |
| U4 `LatticeIndependent` | Equivalence of residual layers of any two coefficient bundles for the same `rho` | elaborates; trio |
| A1' `HasStableLattice` | `Nonempty StableLatticeData`, with the rank-two hypothesis correctly bound | elaborates; trio |
| A3' `HasSemisimplifiedReduction` | Existence of a finite free semisimplified residual model | elaborates; trio |
| M4 `SemisimpleAscendsToResidualClosureContract` | Explicit contract for finite-field scalar-extension of semisimplicity | elaborates; trio |
| L1a `charpoly_baseChange_eq_of_generic` | Generic-fibre equality implies equality after any base change | proved; trio |
| L1b `residual_charpoly_eq_of_two_integral_models` | Two lattices yield equal residual characteristic polynomials | proved; trio |
| A4' `latticeIndependent_of_groupContract` and bundle form | Genuine lattice independence from an explicit BN contract hypothesis | proved; trio |

Universe constraint: for `k = ResidueField O : Type uO`, the bundle-level Brauer–Nesbitt contract
must be instantiated at `GroupContract.{uO, uF, 0, 0}`. The naive universe-zero instantiation fails.

## Separation ladder

The design now keeps five concerns distinct:

1. Stable-lattice existence: `HasStableLattice`, with a separate theorem owner.
2. Continuous residual representation and semisimplification existence:
   `HasSemisimplifiedReduction`, with discrete residual topology explicit.
3. Common residual closure: `AgreeInResidualClosure`, with both embeddings explicit.
4. Raw reduction versus semisimplification: the bundle stores only a semisimplified model.
5. Actual lattice independence: `LatticeIndependent`, wired conditionally through the exact
   Brauer–Nesbitt contract.

The existing same-integral-model predicate `SemisimplifiedResidualModelsUnique` remains a separate,
strictly weaker statement and must not be described as lattice independence.

## Genuine remaining mathematics and owners

| ID | Required theorem | Owner/dependencies |
|---|---|---|
| T-A1 | Stable lattice for every continuous rank-two `rho` | New T1 coefficients node; compactness, open stabilizer, finite-orbit lattice sum, DVR freeness and rank transport |
| T-A2 | Noetherianity, finite residue field, and adic completeness from the minimal coefficient hypotheses | T1 coefficient glue; Mathlib transfer and completeness results |
| T-A3 | Existence of a semisimplified residual model | New T1 coefficients node; finite-length/composition-series construction and continuity |
| M4 | Semisimplicity ascent from finite `k` to its algebraic closure | Brauer–Nesbitt-adjacent node; perfect/separable base change |
| T-IND-CLOSURE | Closure-level comparison for any two coefficient bundles | L1b, M4, algebraically closed BN branch, and residual rank transport |
| BN | `GroupContract` or reviewed branches | `FLT-BRAUER-NESBITT`; consumed only as an explicit hypothesis until discharged |

This resolves the T1/T2 dependency tension without deferral: statements needing Brauer–Nesbitt take
its contract as a named hypothesis, making the dependency visible in their types without extending
their axiom closures.

## Counterexamples guarding the interface

1. A one-dimensional trivial representation refutes any unqualified theorem asserting a rank-two
   stable model for arbitrary `V`; `hV : Module.rank E V = 2` is load-bearing.
2. Distinct stable lattices in a unipotent two-dimensional p-adic representation can have
   non-isomorphic raw reductions but identical semisimplifications. Raw reductions cannot be the
   comparison boundary.
3. For characters over `𝔽_{p²}`, equality after embedding into an algebraic closure depends on the
   chosen embeddings. Closure embeddings must be data.
4. Equal trace alone does not determine characteristic polynomial in small characteristic; full
   characteristic-polynomial equality and rank conditions remain necessary.
5. The valuation ring of `AlgebraicClosure ℚ_[p]` is not a DVR/Noetherian coefficient ring. A
   finite-subextension descent step cannot be omitted.
6. Omitting the maximal-ideal-kernel condition lets the generic fibre masquerade as residual
   reduction.

## Dependency-ordered build graph

```text
MLTSourceBoundary + BrauerNesbittBoundary
  -> MLTCoefficientData probe
       U1/U2/U3/U4, A1'/A3', M4 contract, L1a/L1b, conditional A4'
  -> T-A2 coefficient glue
  -> T-A1 stable-lattice existence
  -> T-A3 semisimplification existence
  -> M4 semisimplicity ascent
  -> T-IND-CLOSURE
  -> Brauer-Nesbitt discharge
  -> MLT/P-adic-Hodge/RACAR/SelectedGood/automorphic consumers
```

## Smallest next probe

Create `FLTMethodology/Probes/MLTCoefficientData.lean`, register it in `FLTMethodology.lean`, and
include U1–U4, A1', A3', M4, L1a, L1b, and both conditional A4' forms with `#check` and
`#print axioms` footers. Every declaration was already tested in temporary files. The gate is:

```text
lake build FLTMethodology.Probes.MLTCoefficientData
```

Every declaration must audit exactly to `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`.

## Stop-losses

- If stable-lattice existence stalls on topology, leave A1' as a named T1 gap; do not substitute a
  historical authority axiom inside this component.
- Any p-adic-Hodge, RACAR, or automorphy vocabulary inside a coefficient unit is a boundary breach.
- If Brauer–Nesbitt narrows to an algebraically closed branch, re-gate A4' through closure ascent and
  descent rather than hiding the mismatch.
- No consumer may instantiate `CoefficientData` with implicit `O`.

This artifact is a design and records kernel-clean temporary probes. It does not itself promote the
component or prove stable-lattice/semisimplification existence.
