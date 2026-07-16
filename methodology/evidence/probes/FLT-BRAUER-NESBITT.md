# FLT-BRAUER-NESBITT boundary probe

Status: **SIGNATURE-GREEN; proof open.** This evidence does not close `FLT-BRAUER-NESBITT`.

## Frozen contract and source route

The full group-representation contract is:

```lean
def GroupContract : Prop :=
  ∀ {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (rho : Representation k G V) (sigma : Representation k G W),
    Representation.IsSemisimpleRepresentation rho →
    Representation.IsSemisimpleRepresentation sigma →
    (∀ g, (rho g).charpoly = (sigma g).charpoly) →
    Nonempty (Representation.Equiv rho sigma)
```

Wiese, *Galois Representations*, Theorem 2.4.6 and Remark 2.4.7, supplies a detailed proof route:

1. replace the algebra by the finite-dimensional joint image and semisimplify;
2. pass to a finite separable splitting field;
3. decompose into simple modules;
4. use Burnside--Frobenius--Schur linear independence of simple characters;
5. in characteristic `p`, show all remaining multiplicities are divisible by `p`, take the unique
   `p`th root of the common characteristic polynomial, and iterate until degree zero;
6. descend the resulting equivalence/composition-factor equality.

For a group algebra it suffices to know characteristic-polynomial equality on group elements. The
trace equality extends linearly to the group algebra; in positive characteristic, the full
characteristic-polynomial hypothesis is retained for the iterative `p`th-root step. It would be
incorrect to claim that characteristic polynomials themselves extend linearly.

Reference: <https://math.uni.lu/~wiese/notes/GalRep.pdf>, Theorem 2.4.6 and Remark 2.4.7.

## Two architectures tested

### A. Full arbitrary-field theorem

This follows the source route above. Pinned Mathlib has semisimple-module decompositions,
isotypic-component APIs, and a product-of-matrix-algebras theorem for finite-dimensional
semisimple algebras over algebraically closed fields. It does not expose the complete terminal
needed here: simple-character independence in the required module form, together with the
splitting-field and descent infrastructure needed by the arbitrary-field proof.

The first absent algebra lemma has the type-correct contract
`SimpleCharactersLinearIndependentContract` in the accompanying Lean probe.

### B. Immediate rank-two odd-characteristic specialization

The current Taylor-2018 boundary is two-dimensional in residual characteristic greater than two.
Over a fixed algebraically closed residual coefficient field, trace equality and simple-character
independence determine multiplicities directly: every multiplicity is at most two and therefore
strictly below the characteristic. This removes the repeated `p`th-root and arbitrary-field descent
tail, but still needs the same simple-character independence/classification terminal.

The exact type-correct specialization is `AlgClosedTwoDimensionalTraceContract`.

## Kernel regression

A tempting one-sided trace weakening is false. Over `ZMod 2`, the trivial representations of the
trivial group in dimensions one and three are semisimple and have equal traces, but cannot be
linearly equivalent. The theorem `refutedOneSidedTraceContract_false` proves the negation in Lean.
Consequently any trace lowering must retain equal rank and the strict characteristic bound; the
original characteristic-polynomial contract already carries the equal-rank information in its
polynomial degree.

## Consumer and kernel evidence

`semisimplifiedResidualModelsUnique_of_groupContract` proves that the full group contract is exactly
sufficient for the current `SemisimplifiedResidualModelsUnique` consumer. It does not assume or
prove Brauer--Nesbitt.

Build command:

```text
lake env lean FLTMethodology/Probes/BrauerNesbittBoundary.lean
```

Expected axiom audit for the proved bridge, trace helper, and finite regression:

```text
[propext, Classical.choice, Quot.sound]
```

## Stop-loss verdict

The full leaf remains open. The smallest implementation route for the immediate Taylor-2018
consumer is the algebraically closed, rank-two, odd-characteristic specialization. Closing even
that route requires a new proof of the simple-character independence/classification terminal in
pinned Mathlib. The broader arbitrary-field theorem additionally requires splitting-field,
positive-characteristic multiplicity descent, and equivalence descent infrastructure.
