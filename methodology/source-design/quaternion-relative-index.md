# Quaternion relative-index definition-of-ready packet

Component: `quaternion-boundary`  
Owner: `FLT-310`  
Obligation: `FLT-HIST-QUATERNION`  
Decision: **PARTIAL - CORRECTED ARCHITECTURE, NOT READY FOR PROVIDER IMPLEMENTATION**

## Exact Lean boundary

The unchanged consumer is the instance:

```lean
instance
    [NumberField.IsTotallyReal F]
    [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (L : LevelStruct F R) (g : GL2 (FiniteAdeleRing (O F) F)) :
    Subgroup.IsFiniteRelIndex Fscalar (L.Delta D g)
```

In the repository's notation, `Fscalar` is the image of `F^x`, `Dscalar` is the image of `D^x`,
`L.UA = L.U sup A_f^x`, and

```text
L.Delta D g = L.UA inf (g^-1 * Dscalar * g).
```

The exact production declaration is
`TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ` in
`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`. Its signature elaborates and its scalar
inclusion is already proved by `LevelStruct.range_units_le_range`; its body currently invokes
`knownin1980s`.

## Source adjudication and correction

- `SRC-017`, Voight Lemma 17.7.13, proves that the norm-one unit group `O^1` of an order in a
  totally definite quaternion algebra is finite.
- `SRC-022`, Voight Lemma 26.5.1, proves the statement actually needed after integral reduction:
  `O^x/R^x` is finite. Its proof uses the norm map, finiteness of `O^1`, and the finite square-class
  quotient `R^x/(R^x)^2` supplied by the unit theorem.
- Neither lemma proves that the adelic stabilizer `L.Delta D g` can be put into an order, nor that
  its quotient by `F^x` maps injectively into `O^x/R^x`. Those are separate bridge obligations.

The current source comment proposes a direct injection

```text
L.Delta D g / F^x  ->  O^1.
```

That step is not valid as stated: rescaling a quaternion unit `d` by `a in F^x` changes its reduced
norm by `a^2`, so a norm-one representative exists only when the relevant norm is a square. The
correct unsplit target is `O^x/(O_F)^x`; equivalently, one may first split into the finitely many
unit square classes and then use `O^1` fibrewise. This corrects the internal architecture without
changing the public theorem.

## Source-to-Lean hypothesis translation

| Mathematical datum | Lean datum or bridge | State |
|---|---|---|
| totally real number field `F` | `[NumberField.IsTotallyReal F]` | exact |
| totally definite quaternion algebra `D/F` | `[IsQuaternionAlgebra F D]`, `[IsQuaternionAlgebra.IsTotallyDefinite F D]` | exact |
| compact open finite-adelic level | `L.U`, `L.isCompact_U`, `L.isOpen_U` | exact |
| adjoining finite-adelic scalar units | `L.UA = L.U sup A_f^x` | exact; `UA` itself is not compact |
| conjugated rational quaternion units | `toConjAct g^-1 • Dscalar` | exact |
| scalar subgroup lies in the intersection | `L.range_units_le_range D g` | proved |
| compact-open containment in a conjugated integral lattice | no exact declaration located | missing |
| intersection with `D` is an `O_F`-order | no quaternion-order construction located | missing |
| quotient-preserving normalization into that order | no declaration located | missing |
| `O^x/(O_F)^x` is finite | exact source at SRC-022; no quaternion-order API located | source fixed, Lean provider absent |

The translation is therefore not complete enough to mark the component definition-ready.

## Corrected acyclic sublemma graph

```text
L.U compact open; conjugate by g
        |
        v
finite-adelic bounded-lattice containment                         OPEN
        |
        v
construct an O_F-order O_g inside D                              OPEN
        |
        +--> every Delta representative is scalar-equivalent
        |    to an element of O_g^x                              OPEN
        |
        +--> kernel of the induced quotient map is exactly F^x  OPEN
                         |
                         v
              Delta/F^x injects into O_g^x/(O_F)^x              OPEN
                         |
             +-----------+-------------------+
             |                               |
             v                               v
       O_g^1 is finite                (O_F)^x/((O_F)^x)^2 finite
       Voight 17.7.13                 Dirichlet unit theorem
             |                               |
             +---------------+---------------+
                             v
                 O_g^x/(O_F)^x finite
                    Voight 26.5.1
                             |
                             v
                 IsFiniteRelIndex Fscalar Delta
```

An alternative route is to work projectively: embed the stabilizer into the intersection of the
discrete diagonal `P(D^x)(F)` with a compact subset of the adelic projective group. That route is
mathematically clean, but the pinned library has neither the required projective quaternion group
nor the adelic discreteness theorem, so it is not currently the shorter Lean route.

## Counterexample and false-weakening review

- Directly mapping the scalar quotient to `O^1` silently assumes that every reduced norm class is a
  square. The norm-square-class term in Voight 26.5.1 is essential.
- Compactness alone does not imply finiteness. A discreteness or open-subgroup argument is required.
- The diagonal copy of `F` in the finite adeles is not discrete by itself. Total definiteness enters
  through the archimedean/projective quotient and cannot be discarded.
- `L.UA` contains the full finite-adelic center and is generally not compact. Any compactness proof
  must first divide out the center or return to `L.U`.
- Conjugation by `g` changes the integral lattice. Reusing the standard matrix order without a
  conjugated-lattice construction is invalid.
- Finiteness of the global double-coset type does not by itself imply finiteness of an individual
  stabilizer quotient.

No counterexample to the exact production instance was found. The counterexample is to the current
comment's proposed intermediate injection, not to the terminal theorem.

## Pinned-library matches

Reusable and already kernel-clean:

- `FLT.Components.QuaternionRelativeIndex.isFiniteRelIndex_of_finite_quotient_model`, which now
  discharges the complete group-index endpoint from a finite target and an exact kernel equation;
- `LevelStruct.range_units_le_range`;
- `LevelStruct.isOpen_UA`, `LevelStruct.isCompact_U`, and conjugation infrastructure;
- `Subgroup.IsFiniteRelIndex.of_isCompact` once a compact subgroup and an open scalar subgroup in
  the correct topology have actually been constructed;
- `NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact` and
  `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`; and
- Mathlib's formal Dirichlet unit theorem, including finite generation of `(O_F)^x` modulo torsion.

The division-algebra cocompactness and finite-double-coset results are genuine reusable
infrastructure, but neither supplies the required finite stabilizer quotient automatically.

Missing after repository and pinned-Mathlib searches:

- a quaternion `O_F`-order abstraction suited to the finite-adelic intersection;
- compact-open containment in one conjugated integral lattice;
- the normalization and quotient injection into `O_g^x/(O_F)^x`;
- reduced norm on units of such an order with the exact kernel `O_g^1`; and
- the assembled finite quotient theorem corresponding to Voight 26.5.1.

## Interfaces to freeze before construction

The next source-reviewed signatures should express, without hiding the conclusion:

```lean
structure IntegralStabilizerModel (L : LevelStruct F R) (g : GL2 (FiniteAdeleRing (O F) F)) where
  OrderUnit : Type*
  instGroup : Group OrderUnit
  scalarUnits : Subgroup OrderUnit
  unitQuotientFinite : Finite (OrderUnit / scalarUnits)
  stabilizerToUnits : (L.Delta D g) ->* OrderUnit
  scalar_preimage : MonoidHom.comap stabilizerToUnits scalarUnits = Fscalar.subgroupOf (L.Delta D g)

theorem finiteRelIndex_of_integralStabilizerModel
    (M : IntegralStabilizerModel L g) :
    Subgroup.IsFiniteRelIndex Fscalar (L.Delta D g)
```

These are architecture sketches, not yet elaboration-audited declarations. The first signature must
be specialized to the repository's quotient APIs and may be split into order construction,
normalization, and kernel lemmas. The generic final implication is now proved and axiom-audited as
`isFiniteRelIndex_of_finite_quotient_model`; the concrete integral-model structure above is not yet
an elaborated declaration.

## Definition-of-ready decision

`PARTIAL`.

The public theorem is still mathematically credible and its exact Lean consumer is stable. The
source route, sublemma graph, false intermediate claim, reusable repository infrastructure, and
missing APIs are now explicit. The pure group-theoretic endpoint is kernel-clean. Provider
implementation must wait until the compact-open-to-order bridge and quotient-injection signatures
are source-reviewed and elaboration-audited. The first new mathematical target should construct the
concrete integral model consumed by `isFiniteRelIndex_of_finite_quotient_model`; it should not be a
direct replacement of `knownin1980s` with an unstructured monolithic proof.
