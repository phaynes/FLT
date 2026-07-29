# Chebotarev rank-two comparison source and implementation packet

Component: `chebotarev`

Obligation: `FLT-CHEBOTAREV`

Decision: **DETERMINISTIC ADAPTER PROVED; ARITHMETIC DENSITY PROVIDER OPEN**

## Exact split

The representation-theoretic conclusion has been separated from the number-theoretic input.

The exact remaining arithmetic proposition is:

```lean
FLT.CompatibleFamily.RatArithmeticFrobeniusConjugacyDensity
```

It says that, for every finite exceptional set of finite places of `ℚ`, the union of the conjugacy
classes of the repository's chosen global images of local **arithmetic** Frobenius elements is dense
in the absolute Galois group. It contains no representation, coefficient, semisimplicity,
characteristic-polynomial, or equivalence conclusion. This file does not assert a witness.

Given density for one exceptional set, the kernel-clean consumer is:

```lean
FLT.CompatibleFamily.nonempty_representationEquiv_of_charFrob_eq_of_density
```

It proves `Nonempty (Representation.Equiv ...)`, not literal equality of Galois representations.

## Literature alignment

- `SRC-019`, Wiese, *Galois Representations*, Theorem 1.2.8 (converted QMD lines 389--397), states
  finite Chebotarev with Frobenius conjugacy classes and positive Dirichlet density.
- `SRC-019`, Corollary 1.2.9 and proof (converted QMD lines 401--411), explains the profinite
  consequence: Frobenius images meet every finite quotient and are dense in the representation
  image.
- `SRC-019`, lines 246 and 266--270, fixes arithmetic Frobenius and explains why choices over one
  prime form a conjugacy class.
- `SRC-013`, Gee Fact 2.27, gives the required conjugacy-saturated Chebotarev density statement;
  Gee Remark 2.31 explicitly states the Chebotarev-plus-Brauer--Nesbitt comparison pattern.
- `SRC-016`, Taylor's automorphy-lifting notes, independently uses the same comparison pattern.

These sources strongly support the exact contract. They are secondary/lecture-note sources for
this purpose; a visually verified primary-source locator has not yet been registered. The user has
authorized progress without primary literature, but the programme's separate historical-assumption
gate remains closed until its stated source and operator conditions are met.

## Kernel-clean deterministic route

```text
equal characteristic polynomials on Frobenius representatives
        |
        +--> characteristic polynomials are conjugacy-invariant
        |
        +--> equality on dense Frobenius conjugacy saturation
        |
        +--> continuous trace and determinant agree everywhere
        |
        +--> rank-two formula reconstructs characteristic polynomials
        |
        +--> proved rank-two Brauer--Nesbitt
        v
Nonempty Representation.Equiv
```

The adapter does not place a topology on polynomials. It extends the two coefficient functions,
trace and determinant, into the Hausdorff coefficient field and then uses the rank-two formula.

## Conditions that remain explicit

- density is for conjugacy saturation, not chosen representatives alone;
- density is asserted after deleting each finite exceptional set;
- the coefficient field is common and Hausdorff;
- both representations are semisimple and rank two;
- equality is of full characteristic polynomials, not traces alone;
- arithmetic/geometric Frobenius normalization is not interchangeable;
- compatibility by itself supplies neither a second representation nor semisimplicity.

## Current boundary

The deterministic definitions and theorems build and audit to exactly
`[propext, Classical.choice, Quot.sound]`. The pinned Mathlib revision contains no global
Chebotarev theorem. Consequently `FLT-CHEBOTAREV` is not yet a proved T3 obligation, and no custom
T2 density axiom has been introduced.
