# Mazur--Serre Frey irreducibility definition-of-ready packet

Component: `mazur`  
Owner: `FLT-301`  
Obligation: `FLT-HIST-MAZUR`  
Decision: **PARTIAL - NOT READY FOR TERMINAL IMPLEMENTATION**

## Exact Lean boundary

The unchanged consumer is:

```lean
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

This signature already elaborates and is audited in
`methodology/evidence/contracts/ExistingAdaptersAudit.lean`. Its present proof uses the generic
`knownin1980s` axiom, so signature existence is not proof completion.

## Exact primary-source chain

- `SRC-020`, Serre 1987, §4.1 Proposition 6, is the exact terminal source. It treats the curve
  `y² = x(x-A)(x+B)` with pairwise-coprime nonzero `A`, `B`, `C`, `A+B+C=0`, the stated parity
  normalization, and prime `p ≥ 5`. It proves that the representation on `p`-division points is
  irreducible.
- `SRC-021`, Serre 1972, Lemmas 5--6 on printed p. 307, supplies the load-bearing character
  dichotomy: for a reducible representation of a semistable elliptic curve, the stable line and
  quotient characters are the trivial and cyclotomic characters in one order or the other.
- `SRC-006`, Mazur 1977, Theorem 8, classifies the rational torsion subgroup and gives the numerical
  upper bound `16` used by Serre.

All three cited pages were checked in primary scans. The earlier source register entry naming only
Mazur's paper was insufficient: Mazur's torsion theorem does not by itself state the Lean terminal.

## Hypothesis translation

| Source hypothesis | Lean data or required bridge | State |
|---|---|---|
| `A+B+C=0`, pairwise coprime, nonzero | take `A = P.a ^ P.p`, `B = P.b ^ P.p`, `C = -(P.c ^ P.p)`; use `P.hFLT`, `P.hgcdab`, `P.hgcdac`, `P.hgcdbc`, nonzero fields | existing arithmetic, adapter proof open |
| `A ≡ -1 (mod 4)` | `P.ha4`, oddness of `P.p`, and exponentiation in `ZMod 4` | bridge open |
| `B ≡ 0 (mod 32)` | `P.hb2`, `P.hp5`, and divisibility of an odd-prime power of an even integer | bridge open |
| curve `y²=x(x-A)(x+B)` | `P.freyCurve` is definitionally the corresponding Weierstrass model up to the sign convention above | exact model audit open |
| prime `p ≥ 5` | `P.pp`, `P.hp5` | exact |
| semistability | `FLTMethodology.Mazur.freyCurve_isSemistableOverQ` proves good or multiplicative reduction of the chosen minimal model at every rational prime | kernel-clean methodology provider |
| full rational 2-torsion | `FLTMethodology.Mazur.freyCurve_hasFullRationalTwoTorsion` explicitly classifies the four points on the transformed model | kernel-clean methodology provider |
| rational `p`-torsion after selecting `E` or `E/X` | Serre 1972 Lemma 6 plus quotient by a rational subgroup | quotient-isogeny API absent |
| rational torsion has order at most 16 | current `Mazur_statement` matches the numerical consequence | named axiom at T2; T3 proof open |

## Acyclic sublemma graph

```text
FreyPackage arithmetic normalization
        |
        +--> explicit Frey model has three distinct rational 2-torsion points
        |
        +--> explicit Frey model is semistable
                    |
reducible p-torsion + p prime
        |
        +--> stable one-dimensional subgroup X
                    |
                    +--> Serre character dichotomy
                              |
                              +--> E has a rational p-point
                              |
                              +--> construct E/X and E/X has a rational p-point
                                             |
odd p-isogeny preserves full rational 2-torsion -+
        |
        v
rational torsion has at least 4*p elements
        |
        +--> 5 ≤ p gives 20 ≤ 4*p
        +--> Mazur Theorem 8 gives torsion size ≤ 16
        v
contradiction, hence FreyPackage.mazur
```

## Counterexample and false-weakening review

- Rational `p`-torsion on `E` handles only the trivial stable-line character. The cyclotomic-line
  case genuinely requires the quotient curve `E/X`; dropping it leaves half the reducible cases.
- A Galois-stable cyclic subgroup is not the same thing as a rational point. The character
  dichotomy is the required bridge.
- The quotient curve must retain all rational 2-torsion. This uses that the quotient isogeny has odd
  degree; it cannot be asserted for an arbitrary isogeny.
- The present `Mazur_statement` uses `Set.ncard`, which is zero on an infinite set. A T3 provider
  must separately establish finiteness or prove the complete classification before using cardinal
  arithmetic.
- Serre's proposition is stated for prime `p ≥ 5`, not only for sufficiently large primes. The
  primary scan confirms the weak inequality, so no special `p=5` escape is needed.
- Semistability is load-bearing. Replacing it by the much weaker statement that the discriminant is
  nonzero does not justify the character dichotomy.

No counterexample to the exact terminal was found. Each rejected weakening above corresponds to a
real missing implication rather than Lean bookkeeping.

## Pinned-library matches

Reusable:

- `FreyPackage`, its pairwise-coprimality lemmas, parity data, and `freyCurve`;
- `GaloisRep.IsIrreducible` and the subrepresentation lattice;
- elliptic-curve rational-point group laws and `twoTorsionPolynomial`;
- `AddCommGroup.torsion`, `Set.ncard`, and finite-cardinality lemmas; and
- the kernel-clean explicit Frey two-torsion provider
  `FLTMethodology.Mazur.freyCurve_hasFullRationalTwoTorsion`; and
- the kernel-clean explicit Frey semistability provider
  `FLTMethodology.Mazur.freyCurve_isSemistableOverQ`; and
- the exact T2 boundary `Mazur_statement`.

Missing:

- quotienting an elliptic curve by a finite Galois-stable subgroup and the induced isogeny;
- the Serre stable-line character dichotomy in repository vocabulary;
- preservation of that 2-torsion under an odd-degree quotient isogeny; and
- a standard-axiom proof of Mazur Theorem 8.

The current and isolated latest-Mathlib scans found no quotient-isogeny API that closes the
remaining geometric gap. The existing minimal-model reduction API was sufficient to construct the
concrete Frey semistability provider below.

## Definition-of-ready decision

`PARTIAL`.

The first interface tranche is now kernel-clean in
`FLTMethodology/Probes/MazurSourceBoundary.lean`:

- `IsSemistableOverQ` quantifies over every rational prime and uses the existing minimal-model
  reduction API to say good or multiplicative reduction;
- `RationalTorsionBound16` strengthens the current `Mazur_statement` boundary with the missing
  finiteness fact, so `Set.ncard` cannot close the theorem vacuously;
- `HasFullRationalTwoTorsion` and `HasLargeRationalTorsion` freeze the exact cardinal outputs used
  by Serre's argument;
- `SemistableReducibleCharacterDichotomy` exposes an injective stable line, a surjective quotient,
  exactness, and the two possible trivial/cyclotomic character orders; and
- `not_hasLargeRationalTorsion_of_bound16` proves the final `4p > 16` contradiction for `p ≥ 5`.

Every declaration above has only `[propext, Classical.choice, Quot.sound]`. In particular, the
terminal numerical contradiction is no longer part of the mathematical risk.

The next elementary provider is also kernel-clean in
`FLTMethodology/Probes/FreyTwoTorsionBoundary.lean`:

- the three affine points corresponding to `X = 0`, `X = a^p`, and `X = -b^p` are constructed on
  the transformed Frey model;
- each is killed by two;
- every rational point killed by two is classified by the exact factorization
  `x * (4*x-a^p) * (4*x+b^p) = 0`; and
- nonzero Frey-package fields plus `a^p+b^p=c^p` prove that the four points are distinct.

Consequently `freyCurve_hasFullRationalTwoTorsion` proves the exact
`HasFullRationalTwoTorsion P.freyCurve` contract with only
`[propext, Classical.choice, Quot.sound]`. This removes the earlier construction-API risk rather
than merely freezing its signature.

The concrete semistability provider is now kernel-clean in
`FLTMethodology/Probes/FreySemistabilityBoundary.lean`:

- at a prime dividing `a*b*c`, pairwise coprimality and the two explicit `c₄` formulas prove that
  `c₄` is a local unit;
- away from that support, the explicit discriminant identity proves that the discriminant is a
  local unit;
- both unit facts are transported through the integral model to the chosen minimal model; and
- every rational prime therefore has good or multiplicative reduction.

Thus `freyCurve_isSemistableOverQ` proves the exact `IsSemistableOverQ P.freyCurve` contract with
only `[propext, Classical.choice, Quot.sound]`, including the prime `2` case. This closes the
semistability construction boundary rather than leaving it as a source-level assertion.

The exact terminal source, primary intermediate sources, consumer signature, proof architecture,
counterexample review, and library gap analysis are now fixed. Provider construction must not begin
as one monolithic proof. The next definition-ready units are, in order:

1. prove that reducibility of the concrete `p`-torsion representation supplies
   `SemistableReducibleCharacterDichotomy`;
2. freeze and implement an `EllipticCurveQuotientIsogenyContract` for the cyclotomic-line case;
3. prove odd-degree quotient isogenies preserve full rational two-torsion and that either character
   case supplies `HasLargeRationalTorsion`; and
4. replace `Mazur_statement` by a provider of `RationalTorsionBound16`.

Only after the remaining geometric signatures elaborate and are source-reviewed should `FreyPackage.mazur` move
from `PARTIAL` to `READY` for provider implementation.
