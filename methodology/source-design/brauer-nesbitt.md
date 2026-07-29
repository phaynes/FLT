# Brauer–Nesbitt source and implementation packet

Component: `brauer-nesbitt`  
Owner: `FLT-309`  
Obligation: `FLT-BRAUER-NESBITT`  
Decision: **PROVED FOR THE FLT-SCOPED RANK-TWO BOUNDARY; PRIMARY-SOURCE LOCATOR OPEN**

## Exact Lean boundary

The theorem used by the FLT programme is:

```lean
FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two
```

It quantifies over an arbitrary field and group, two finite-dimensional
semisimple representations of finrank exactly two, and equality of their
characteristic polynomials on every group element. It concludes
`Nonempty (Representation.Equiv rho sigma)`.

The reusable contract and its kernel-clean witness are:

```lean
FLT.Components.BrauerNesbitt.RankTwoContract
FLT.Components.BrauerNesbitt.rankTwoContract
```

The general-dimensional `FLT.Components.BrauerNesbitt.Contract` remains a
separate unproved proposition. It is not needed by the presently encoded FLT
consumers and is not counted as completed.

## Source adjudication

- `SRC-019`, Wiese Theorem 2.4.6 and Remark 2.4.7(iii), gives the modern
  arbitrary-field statement and a detailed secondary-source proof route.
- `SRC-018`, Brauer–Nesbitt 1937, is genuine primary provenance but assumes an
  algebraically closed field and does not state the modern arbitrary-field
  group contract.
- An exact primary-source locator for the unchanged modern formulation remains
  open. Per the programme's current policy, this is recorded as literature
  assurance debt rather than used to erase a kernel-checked theorem.

## Hypothesis translation

| Mathematical condition | Lean boundary | Status |
|---|---|---|
| arbitrary coefficient field | `[Field k]` | exact |
| arbitrary group | `[Group G]` | exact |
| finite-dimensional representations | `Module.Finite k V`, `Module.Finite k W` | exact |
| rank two | `Module.finrank k V = 2`, `Module.finrank k W = 2` | exact and FLT-scoped |
| semisimple | `Representation.IsSemisimpleRepresentation` | exact |
| identical characteristic polynomials on every group element | `∀ g, (rho g).charpoly = (sigma g).charpoly` | exact |
| equivalence of representations | `Nonempty (Representation.Equiv rho sigma)` | exact |

## Proved architecture

```text
charpoly equality on group elements
        |
        +--> trace and determinant equality
        |
        +--> degree-two Amitsur identity
                 |
                 v
      charpoly equality on joint-image algebra
                 |
                 +--> joint-image algebra is semisimple
                 |
                 +--> Wedderburn–Artin matrix/division-ring blocks
                 |
                 +--> central-idempotent charpolys recover block ranks
                 |
                 +--> Morita reconstruction and blockwise equivalence
                 v
      joint-image linear equivalence
                 |
                 v
      Representation.Equiv                          PROVED
```

The degree-two determinant identity is denominator-free, so the proof does not
require interpolation, a large or perfect field, algebraic closure, or a
characteristic restriction. The Wedderburn decomposition retains possibly
noncommutative division rings.

## Direct consumer

`FLTMethodology.Taylor2018.Coefficients.latticeIndependent_rankTwo` consumes
the theorem without accepting a Brauer–Nesbitt proposition as an assumption.
The existing coefficient bundles supply semisimplicity, both rank-two facts,
and characteristic-polynomial equality on every Galois element.

The compatible-family use remains conditional on `FLT-CHEBOTAREV`, which owns
the distinct passage from almost-all Frobenius data to equality on every group
element.

## Counterexample and stop-loss boundaries

- Trace equality alone is false in positive characteristic; the `ZMod 2`
  regression remains in the repository.
- Characteristic polynomials cannot be extended linearly. Only the trace and,
  in dimension two, the denominator-free determinant identity are used.
- The result does not establish the general-dimensional `Contract`.
- It does not establish Chebotarev or any consumer's separate semisimplicity,
  rank, or characteristic-polynomial premise.

## Verification

- Targeted provider build: 2,322 jobs, success.
- Direct consumer build: 3,851 jobs, success.
- `lake build FLT FLTMethodology`: 9,043 jobs, success.
- Provider and consumer axiom closure:
  `[propext, Classical.choice, Quot.sound]`.
- Fresh GPT-5.6 xhigh theorem review: `PASS`.
- Fresh GPT-5.6 xhigh consumer review: `PASS`.
- Fable 5 static mathematical review: positive, but its executable phase was
  unavailable and is not counted as an approval.

The complete evidence packet is
`methodology/evidence/probes/FLT-BRAUER-NESBITT-RANK-TWO-20260730.md`.

## Disposition

The FLT-scoped rank-two obligation is implementation-complete and may be shown
as proved after the control-record change passes independent review. The exact
primary-source locator remains a visible literature-assurance gap. The next
mathematical comparison gate is `FLT-CHEBOTAREV`, not more Brauer–Nesbitt proof
work.
