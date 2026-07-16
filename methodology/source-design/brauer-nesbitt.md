# Brauer--Nesbitt definition-of-ready packet

Component: `brauer-nesbitt`  
Owner: `FLT-309`  
Obligation: `FLT-BRAUER-NESBITT`  
Decision: **PARTIAL - NOT READY FOR TERMINAL IMPLEMENTATION**

## Exact Lean boundary

The production contract is:

```lean
FLT.Components.BrauerNesbitt.Contract
```

It quantifies over an arbitrary field and group, two finite-dimensional semisimple
representations, equality of their characteristic polynomials on every group element, and concludes
that the representations are linearly equivalent. No finiteness, topology, perfectness, algebraic
closure, characteristic-zero, or trace-only assumption is present.

The contract and its finite joint-image reduction elaborate in
`FLT/Components/Contracts/BrauerNesbitt.lean`. Their audit is
`methodology/evidence/contracts/BrauerNesbittContractAudit.lean`.

## Source adjudication

- `SRC-019`, Wiese Theorem 2.4.6 and Remark 2.4.7(iii), gives the exact modern statement and a
  detailed proof route, but is a secondary source.
- `SRC-018`, Brauer--Nesbitt 1937, was checked against all five scanned pages. It assumes an
  algebraically closed field and studies regular representations, radicals, indecomposable
  constituents, and symmetric/Frobenius algebras. It does not state the unchanged modern
  arbitrary-field group contract.
- Consequently the component still lacks the exact primary theorem locator demanded by FLT-205.
  The name of a historical paper is not being treated as source equivalence.

## Hypothesis translation

| Source notion | Lean boundary | Status |
|---|---|---|
| arbitrary coefficient field | `[Field k]` | exact |
| arbitrary group | `[Group G]` | exact |
| finite-dimensional representations | `Module.Finite k V`, `Module.Finite k W` | exact |
| completely reducible/semisimple | `Representation.IsSemisimpleRepresentation` | exact |
| identical characteristic polynomials at every group element | `∀ g, (rho g).charpoly = (sigma g).charpoly` | exact |
| equivalence of representations | `Nonempty (Representation.Equiv rho sigma)` | exact |

## Banked proof graph

```text
characteristic-polynomial equality
        |
        +--> trace_eq_of_charpoly_eq                         PROVED
        |
        +--> jointImagePoint / jointImageSpan                PROVED
                  |
                  +--> jointImageAlgebra                     PROVED
                  +--> both projection homomorphisms         PROVED
                  +--> actual group-element embedding        PROVED
                  +--> basis selected from group image       PROVED
                              |
                              v
                     FiniteJointImageContract                OPEN
                              |
                              v
                     Contract                                REDUCTION PROVED
```

The remaining theorem is finite-dimensional but still mathematical: prove that two semisimple
modules over the finite joint-image algebra have identical simple multiplicities from the retained
characteristic-polynomial data.

## Intended terminal architecture

1. Pass both actions through the finite joint-image algebra already constructed.
2. Transport semisimplicity from the group representations to modules over this algebra.
3. Quotient by the Jacobson radical, or work componentwise with the semisimple action algebra.
4. Use central/simple-component projectors to recover every composition multiplicity from the
   characteristic-polynomial data without assuming a separable splitting field.
5. Construct the module equivalence and transport it back to a `Representation.Equiv`.

Step 4 is the first missing theorem. It must be source-checked over imperfect fields before its Lean
signature is frozen.

## Counterexample and stop-loss review

- Trace equality alone is false in positive characteristic: the existing `ZMod 2` regression uses
  trivial representations in dimensions one and three.
- Characteristic polynomials do not extend linearly from group elements to group-algebra elements.
  Only trace equality is extended linearly.
- A finite separable splitting-field proof does not cover arbitrary imperfect fields.
- The algebraically closed, two-dimensional, odd-characteristic shortcut covers only the residual
  coefficient consumer. It does not cover the characteristic-zero compatible-family consumer.
- Chebotarev is separate: almost-all Frobenius equality is not the all-group-elements hypothesis of
  this contract.

No counterexample to the unchanged contract was found. The rejected weakenings remain recorded so
they cannot re-enter through a downstream convenience lemma.

## Pinned-library matches

Reusable:

- `Representation.IsSemisimpleRepresentation`;
- `Submodule.exists_fun_fin_finrank_span_eq`;
- `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` for the algebraically closed branch;
- `LinearMap.trace_eq_matrix_trace` and characteristic-polynomial/trace bridges; and
- semisimple-module and isotypic-component APIs.

Missing:

- arbitrary-field Brauer--Nesbitt;
- the finite joint-image multiplicity terminal;
- a componentwise imperfect-field descent theorem; and
- the separate Chebotarev continuity bridge.

The isolated current-Mathlib scan at commit `15e888f098dc8d8844f935ca6a12bae4d4582bff`
found no new exact Brauer--Nesbitt declaration; the proof must therefore be supplied locally or by a
later dependency upgrade.

## Definition-of-ready decision

`PARTIAL`.

The contract, hypothesis translation, counterexample review, library survey, and finite reduction
are ready and kernel-clean. Terminal construction is blocked on two exact items:

1. an exact primary-source locator for the arbitrary-field theorem or an independently reviewed
   source for the finite-algebra terminal; and
2. an elaborating signature and proof outline for the imperfect-field-safe multiplicity theorem.

The next theorem to freeze is the finite-algebra multiplicity terminal, not a weakened residual-only
replacement.
