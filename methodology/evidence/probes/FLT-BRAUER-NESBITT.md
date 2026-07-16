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

Wiese, *Galois Representations*, Theorem 2.4.6 gives the arbitrary-field algebra-element theorem,
and Remark 2.4.7(iii) states the group-element specialization. The following splitting-field route
is sound over perfect coefficient fields:

1. replace the algebra by the finite-dimensional joint image and semisimplify;
2. pass to a finite separable splitting field;
3. decompose into simple modules;
4. use Burnside--Frobenius--Schur linear independence of simple characters;
5. in characteristic `p`, show all remaining multiplicities are divisible by `p`, take the unique
   `p`th root of the common characteristic polynomial, and iterate until degree zero;
6. descend the resulting equivalence/composition-factor equality.

For a group algebra it suffices to know characteristic-polynomial equality on group elements. The
trace equality extends linearly to the group algebra; in positive characteristic, the full
characteristic-polynomial hypothesis is retained for the iterative `p`th-root step. This is the
repair needed to make the terse basis remark precise; characteristic polynomials themselves do not
extend linearly.

The displayed splitting-field route is not complete over an arbitrary imperfect field: a finite
purely inseparable field extension need not admit the finite separable splitting field it uses.
The full `GroupContract` remains true, but its arbitrary-field proof must instead work through the
finite-dimensional semisimple joint image with a spanning-set Brauer--Nesbitt argument, or supply a
separate component-wise descent proof. Wiese is a detailed secondary source; the exact primary
source for that arbitrary-field proof remains a source gate.

Reference: <https://math.uni.lu/~wiese/notes/GalRep.pdf>, Theorem 2.4.6 and Remark 2.4.7.

## Kernel-clean joint-image reduction

The arbitrary-field route is now reduced, without changing `GroupContract`, to the exact
`FiniteJointImageContract`. The probe constructs:

- the finite-dimensional subalgebra of `End(V) × End(W)` spanned by pairs `(rho g, sigma g)`;
- both projection algebra homomorphisms;
- the embedded element for each actual group element; and
- `exists_jointImage_basis_from_group`, a linearly independent spanning family of genuine group
  image pairs indexed by the finrank of the joint-image span.

`groupContract_of_finiteJointImageContract` is kernel-clean and proves that the finite remainder is
sufficient for the unchanged full contract. The residual proposition remains substantive: from
semisimplicity, characteristic-polynomial equality on all group elements, and the extracted finite
basis, prove the representation equivalence. No `sorryAx` is hidden in the reduction.

Two further bridges are now kernel-clean. `trace_asAlgebraHom_eq` extends trace equality on group
elements linearly to every element of the group algebra. `prodAsModuleEquiv` identifies the module
of the product representation with the product of the two individual representation modules;
`prod_asAlgebraHom_apply` supplies its load-bearing action calculation. These remove the group-
algebra linearity and product-module API gaps. They do not prove the remaining central isotypic-
projector/simple-character theorem.

## Two architectures tested

### A. Full arbitrary-field theorem

Pinned Mathlib has semisimple-module decompositions, isotypic-component APIs, and a
product-of-matrix-algebras theorem for finite-dimensional semisimple algebras over algebraically
closed fields. It does not expose the arbitrary-field spanning-set Brauer--Nesbitt terminal or the
component-wise descent needed to prove `GroupContract`. The next full-route contract must be frozen
only after its arbitrary-field proof architecture and primary source are selected.

### B. Immediate rank-two odd-characteristic specialization

The current Taylor-2018 boundary is two-dimensional in residual characteristic greater than two.
Over a fixed algebraically closed residual coefficient field, trace equality and simple-character
independence determine multiplicities directly: every multiplicity is at most two and therefore
strictly below the characteristic. This removes the repeated `p`th-root and arbitrary-field descent
tail. Its first absent terminal is `SimpleCharactersLinearIndependentContract`.

The exact type-correct specialization is `AlgClosedTwoDimensionalTraceContract`.
The kernel-clean `specializedResidualModelsUnique` bridge shows that it discharges the residual
consumer after adding a common algebraically closed field, rank two for both spaces, and odd
positive characteristic. The generic `SemisimplifiedResidualModelsUnique` consumer does not expose
those hypotheses, and the separate compatible-family terminal has only almost-all Frobenius data
until its Chebotarev bridge is built. The specialization therefore does not yet replace the generic
graph obligation.

The rank-two residual hypothesis is no longer merely anticipated. The kernel-clean theorem
`residualModel_finrank_eq_two` derives it from integral rank two and the existing residual-model
characteristic-polynomial comparison at the identity. Independent Fable 5 and GPT-5.6 xhigh
consumer reviews nevertheless returned **NARROWING PARTIAL ONLY**: the characteristic-zero
compatible-family branch cannot use the odd residual-characteristic theorem, and it still lacks
the Chebotarev/continuity and semisimplicity bridge from almost-all Frobenius data.

## Kernel regression

A tempting one-sided trace weakening is false. Over `ZMod 2`, the trivial representations of the
trivial group in dimensions one and three are semisimple and have equal traces, but cannot be
linearly equivalent. The theorem `refutedOneSidedTraceContract_false` proves the negation in Lean.
Consequently the tested one-sided trace lowering must retain equal rank and a bound on both spaces.
This regression does not independently prove that the strict characteristic bound is necessary;
the original characteristic-polynomial contract already carries equal-rank information in its
polynomial degree.

## Consumer and kernel evidence

`semisimplifiedResidualModelsUnique_of_groupContract` proves that the full group contract is
sufficient for the current `SemisimplifiedResidualModelsUnique` consumer. It does not assume or
prove Brauer--Nesbitt.

Build command:

```text
lake env lean FLTMethodology/Probes/BrauerNesbittBoundary.lean
```

Expected axiom audit for the proved bridges, joint-image reduction, trace and product-module
helpers, and finite regression:

```text
[propext, Classical.choice, Quot.sound]
```

## Stop-loss verdict

The full leaf remains open. Because the current consumers need two different coefficient regimes,
the next graph gate remains the arbitrary-field `GroupContract` or an exact two-branch replacement.
Its proof needs a source-checked finite-dimensional joint-image/spanning-set argument rather than
the incomplete separable splitting-field route. The reviewed algebraically closed rank-two route
may serve only the residual branch; it still requires a proof of the simple-character
independence/classification terminal in pinned Mathlib. The characteristic-zero compatible-family
branch remains a separate theorem rather than a hidden narrowing.
