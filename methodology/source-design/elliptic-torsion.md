# Elliptic-curve torsion source and proof design

Status: `PARTIAL`
Owner work item: `FLT-401`
Obligation: `FLT-TATE-TORSION`
Frozen provider file: `FLT/EllipticCurve/Torsion.lean`

## Exact frozen boundary

The provider file now has exactly two admissions:

```lean
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n)

theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n ^ 2
```

The earlier five-admission count is stale. The remaining Galois-action and group-theory code in
this file is kernel-clean, but `WeierstrassCurve.galoisRep` still transitively consumes
`n_torsion_finite`.

## Mathematical source contract

The clean conceptual source route is the multiplication morphism on an elliptic curve, viewed as
a one-dimensional abelian variety:

1. Stacks Project, Lemma 39.9.8, tag `0BFG`: multiplication by `n` on an abelian variety is finite
   locally free of degree `n ^ (2 * dim A)`. For an elliptic curve the degree is `n ^ 2`.
2. Stacks Project, Lemma 39.9.9, tag `0BFH`: multiplication by `n` is étale exactly when `n` is
   invertible in the base field.
3. Stacks Project, Example 58.5.1, tag `0BN8`, together with Lemma 29.37.7, tag `02GL`: finite étale
   schemes over a separably closed field are finite disjoint unions of rational points.

These results justify both frozen declarations. They do not directly instantiate the current Lean
types: neither the pinned Mathlib nor current Mathlib master has a Weierstrass-curve scheme, its
multiplication morphism, or the bridge from that scheme's rational points to
`WeierstrassCurve.Affine.Point`.

## Current library boundary

Reusable in the pinned library:

- `WeierstrassCurve.ΨSq`, `WeierstrassCurve.Φ`, and their degree and leading-coefficient theorems;
- `WeierstrassCurve.ΨSq_ne_zero` when `(n : k) ≠ 0`;
- the complete affine point type and group law;
- finite polynomial root sets; and
- the exact quadratic Weierstrass equation in the y-coordinate.

Absent in both the pinned Mathlib commit and current master at
`16274bd25ac511707d2242a6c762e67a48ea46f7`:

- `n • P = 0 ↔ (E.ΨSq n).eval P.x = 0` for nonzero affine points;
- the more general rational formula for the x-coordinate of `n • P` using `Φ n / ΨSq n`;
- a Weierstrass-curve scheme and multiplication-by-`n` morphism; and
- a point-count bridge from a finite étale kernel of degree `n ^ 2` to the repository point type.

## Kernel-clean decomposition now established

`FLTMethodology/Probes/EllipticTorsionSourceBoundary.lean` proves:

```lean
theorem n_torsion_finite_of_detector
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (D : TorsionXDetector E n) : Finite (E.nTorsion n)

def PsiSqDetectsNTorsion
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop

def DivisionPolynomialXFormula
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop

theorem psiSqDetectsNTorsion_of_xFormula
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hx : DivisionPolynomialXFormula E n) : PsiSqDetectsNTorsion E n

def DivisionPolynomialXRelation
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop

def DivisionPolynomialXHomogeneous
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] (n : ℕ) : Prop

theorem divisionPolynomialXFormula_of_xRelation
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hr : DivisionPolynomialXRelation E n) : DivisionPolynomialXFormula E n

theorem addX_mul_addNegX_kummer
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] ... :
    xplus * xminus * (x₁ - x₂) ^ 2 = kummerBiquadratic E x₁ x₂

theorem n_torsion_finite_of_psiSq_detection
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    Finite (E.nTorsion n)

theorem divisionPolynomialXHomogeneous_nat ... (n : ℕ) :
    DivisionPolynomialXHomogeneous E n

theorem divisionPolynomialXRelation_nat ... (n : ℕ) :
    DivisionPolynomialXRelation E n

theorem psiSqDetectsNTorsion_nat ... (n : ℕ) :
    PsiSqDetectsNTorsion E n

theorem n_torsion_finite_prime_to_char ... {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (E.nTorsion n)

theorem psiSq_ne_zero_all_characteristics ... {n : ℕ} (hn : 0 < n) :
    E.ΨSq (n : ℤ) ≠ 0

theorem n_torsion_finite_all_characteristics ... {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n)

theorem psiSqDetectsNTorsion_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 2

theorem divisionPolynomialXFormula_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    DivisionPolynomialXFormula E 2

theorem psiSqDetectsNTorsion_three
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 3

theorem prePsiFour_eval_eq_psiTwo_double ...

theorem psiSqDetectsNTorsion_four
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 4
```

The proof is elementary and standard-axiom clean. It bounds x-coordinates by roots of the detector
polynomial, then bounds each y-fibre by the roots of a nonzero monic quadratic. Thus the
characteristic-prime-to-`n` finiteness lane is reduced to the single exact dictionary proposition
`PsiSqDetectsNTorsion`.

The stronger sufficient contract `DivisionPolynomialXFormula` is now explicit and kernel-cleanly
connected to the detector: whenever `ΨSq n` is nonzero at an affine point, `n • P` has x-coordinate
`Φ n / ΨSq n`, so an `n`-torsion point would otherwise be a nonzero affine point equal to infinity.
The complete `n = 2` instance of this stronger contract is also kernel-clean. Its proof uses the
actual affine doubling law, proves the tangent denominator nonzero from `ΨSq 2 ≠ 0`, and derives the
`Φ 2 / ΨSq 2` coordinate identity from the Weierstrass equation. This replaces an informal
fallback suggestion with a tested Lean interface and confirms that self-base-change and dependent
point-proof normalization do not obstruct the intended general theorem.

For the induction itself, `DivisionPolynomialXRelation` now supplies a denominator-free contract:
if `n • P` is infinity it asserts `ΨSq n = 0`; if it is affine with x-coordinate `xₙ`, it asserts
`xₙ * ΨSq n = Φ n`. This single match covers both branches that otherwise force repeated denominator
case splits. Kernel-clean adapters derive both the exact x-coordinate formula and the torsion
detector from it. The relation is proved for `n = 0,1,2`; therefore the new recurrence interface is
tested across infinity, identity, vertical-doubling, and nonvertical-doubling branches.

`DivisionPolynomialXHomogeneous` is a branch-free equivalent using Mathlib's existing
`Affine.Point.xRep` Kummer coordinate. For `Q = n • P` it states

```text
Q.xRep[0] * ΨSqₙ(x) = Q.xRep[1] * Φₙ(x).
```

At infinity `xRep = [1,0]`, so this is `ΨSqₙ(x)=0`; at an affine point `xRep = [x(Q),1]`,
so it is the cross-multiplied x-coordinate formula. Both directions of equivalence to the
match-based relation are kernel-clean. This is the preferred induction statement because it
eliminates branch syntax from the algebraic recurrence.

The apparent need for a separate y-coordinate division polynomial has also been removed from the
design. `addX_mul_addNegX_kummer` proves the generalized-Weierstrass differential-addition identity
for two affine points with distinct x-coordinates: the product of the x-coordinates of `P + Q` and
`P - Q`, after multiplying by `(x(P)-x(Q))²`, is the biquadratic expression

```text
x(P)² x(Q)² - b₄ x(P)x(Q) - b₆(x(P)+x(Q)) - b₈.
```

The proof expands the actual affine slopes and uses both Weierstrass equations; its axiom closure is
the standard trio. This is the x-only differential-addition primitive required by an adjacent-pair
or Montgomery-ladder induction. No `ωₙ` library needs to be invented merely to close the x-coordinate
dictionary. At that layer the degenerate equal-x and infinity branches required explicit cases.
The corresponding bihomogeneous form is also kernel-clean, including its scaling law, symmetry,
affine specialization, and infinity specializations. Consequently recurrence algebra can now be
performed directly on representative pairs `[X,Z]`, without dividing by `Z` or losing the infinity
case.

`FLTMethodology/Probes/KummerAddSubPoint.lean` now closes those point-level cases. It proves the
missing symmetric-sum affine identity, then proves that Mathlib's `addSubMap`, evaluated on
`P.sym2x Q`, is projectively equivalent to `(P + Q).sym2x (P - Q)` for every pair of points. The
proof covers distinct x-coordinates by exact scaling with `(x(P)-x(Q))²`; the equal-x case is
reduced to the already kernel-clean `n = 2` homogeneous division-polynomial relation, so doubling,
inverse, and two-torsion branches do not cancel a possibly zero tangent denominator. One or both
points at infinity are proved separately. The exported theorem has only the standard axiom trio.

The complete Kummer matrix, rather than only its product entry, is now the induction boundary. Its
middle bihomogeneous entry is

```text
2 X₁X₂(X₁Z₂ + X₂Z₁) + b₂X₁X₂Z₁Z₂
  + b₄(X₁Z₂ + X₂Z₁)Z₁Z₂ + b₆(Z₁Z₂)².
```

Its scaling, symmetry, infinity, and polynomial-evaluation laws are kernel-clean. The coefficient
of the final term is `b₆`, not `2b₆`: the latter tempting transcription is refuted already at
`n = 1`, while the corrected form specializes exactly to `Ψ₂Sq` when `P - P` is infinity.

The polynomial normalization boundary is now explicit rather than implicit. The methodology probe
defines `kummerBiquadraticPolynomial`, proves that evaluation recovers the scalar bihomogeneous
form, and proves for every integer `n` the parity-normalization identity

```text
(X * ΨSqₙ - Φₙ)² = ΨSqₙ₊₁ * ΨSqₙ₋₁.
```

Thus the coordinate-gap denominator is no longer an open part of the recurrence. The remaining
pure polynomial statement is named `KummerDivisionPolynomialRecurrence`; it says that applying the
Kummer biquadratic to `[Φₙ,ΨSqₙ]` and `[X,1]` gives `Φₙ₊₁Φₙ₋₁`. Its complete base
block `n = 0,1,2,3,4` is kernel-clean. The initially disproportionate coefficient expansions at
`n = 3,4` were reduced to explicit multiples of the genuine generalized-Weierstrass invariant
relation `b₂b₆ - b₄² - 4b₈ = 0`; Lean checks those factorizations. The next implementation should use
the binary `normEDSRec` structure for the arbitrary index, not repeat coefficient expansion.
The exact remaining branches are now named `KummerDivisionPolynomialEvenStep` and
`KummerDivisionPolynomialOddStep`, and a kernel-clean assembly theorem proves the recurrence at
every natural index from those two contracts plus the five closed bases.

The companion `KummerDivisionPolynomialMiddleRecurrence` states that the matrix's middle entry is
the symmetric cross term

```text
Φₙ₊₁ ΨSqₙ₋₁ + ΨSqₙ₊₁ Φₙ₋₁.
```

Its full `n = 0,1,2,3,4` base block is also kernel-clean; the nontrivial bases factor through the
same `b₂b₆ - b₄² - 4b₈ = 0` invariant. `KummerDivisionPolynomialLadder` synchronizes the product
and middle entries, with the denominator entry already supplied for every integer by the squared
coordinate-gap theorem. Exact synchronized even/odd step contracts and an all-natural-index
assembly theorem are kernel-clean. The concrete step implementations are now kernel-clean as well:
`PrePsiWindowAlgebra` isolates four generic ideal-membership certificates, while
`PrePsiWindowSteps` attaches them to Mathlib's binary `preΨ` recursion in both center parities.
Consequently the synchronized Kummer ladder is now unconditional at every natural index.

Those steps now have a smaller sufficient invariant. `PrePsiWindowRelation E n` consists of two
five-term equations: Ward's product relation for `preΨ(n±2)` and a symmetric-sum companion for
`preΨ(n±2)` weighted by `preΨ(n±1)²`. A kernel-clean theorem proves that this pair implies both
entries of `KummerDivisionPolynomialLadder E n` in each parity class. The proof is a short linear
combination, so it avoids expanding any high-index division polynomial. The next mathematical
obligation was consequently the reusable statement `∀ n, PrePsiWindowRelation E n`. Its full
`n = 0,1,2,3,4` base block, concrete binary even/odd steps, `normEDSRec` assembly, and direct
assembly into the Kummer ladder are now kernel-clean. The public exports include the all-natural
window theorem and both product and middle Kummer recurrences.

A scratch algebra audit also rejected a tempting under-strength implementation tactic: treating
five neighboring Kummer recurrence equalities as relations for an otherwise arbitrary sequence
does not reduce the even target to zero. The concrete `preΨ` values carry additional normalized-EDS
history. The corrected two-equation window state is sufficient and is now proved at every natural
index by unfolding the actual binary `preΨ_even`/`preΨ_odd` construction. The failed product-only
classifier remains useful negative evidence: downstream work must consume the complete window or
the exported synchronized ladder, not reconstruct an under-strength abstract induction state.

The full `n = 0,1,2,3` base block and the first recursive even case `n = 4` are kernel-clean. The
first two cases are structural. The `n = 2`
case derives the fixed-point condition
under affine negation from `2 • P = 0`, expands `Ψ₂Sq`, and eliminates the Weierstrass equation. The
second passes through the nonvertical affine doubling formula, clears its tangent denominator, and
derives the `Ψ₃` equation. The `n = 4` proof then splits on whether the point is already two-torsion,
doubles the remaining case, and consumes the separately named `preΨ₄`/doubled-`ψ₂` identity. Together
they confirm the detector interface's normalization and point representation in both parity classes
and validate one recurrence-shaped step. The later Kummer ladder and projective propagation modules
now subsume these isolated base-case proofs with an all-natural-index result.

`FLTMethodology/Probes/KummerProjectivePropagation.lean` now closes the integration layer. It proves
that every evaluated representative `![(E.Φ n).eval x, (E.ΨSq n).eval x]` is nonzero by induction
through Mathlib's `addSubMap_ne_zero`; no universal resultant hypothesis is needed. Generic
two-coordinate scaling and symmetric-pair cancellation lemmas then transport projective equality
through the homogeneous map. A two-step induction combines those lemmas with the unconditional
polynomial ladder and the all-point add/sub theorem to prove, for every natural `n`:

```lean
divisionPolynomialXHomogeneous_nat E n
divisionPolynomialXRelation_nat E n
psiSqDetectsNTorsion_nat E n
```

The same module exports `n_torsion_finite_prime_to_char`, so the complete
characteristic-prime-to-`n` finiteness lane is kernel-clean. All load-bearing exports have exactly
the standard axiom trio.

`FLTMethodology/Probes/PsiSqAllCharacteristic.lean` removes the remaining characteristic
restriction. The new argument assumes `ΨSqₙ = 0`, base-changes to an algebraic closure, and chooses
a root of the universally monic positive-degree polynomial `Φₙ`. At that root both coordinates of
the evaluated division-polynomial representative would vanish, contradicting
`divisionPolynomialRep_ne_zero`. Therefore `ΨSqₙ` is nonzero for every positive `n` in every
characteristic. Combining this fact with `psiSqDetectsNTorsion_nat` and the finite detector assembly
proves the exact frozen finiteness signature in the methodology tree:

```lean
theorem n_torsion_finite_all_characteristics
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n)
```

This theorem has only the standard axiom trio. Provider migration remains a separately authorized
change, and the exact `n ^ 2` count is still open.

## Minimal implementation graph

Build in this order:

1. `FLT-TORSION-Y-FIBER` — closed in the methodology probe: a fixed x-coordinate has finitely many
   affine y-coordinates.
2. `FLT-TORSION-DETECTOR-FINITE` — closed in the methodology probe: any nonzero x-coordinate
   detector makes `E[n](k)` finite.
3. `FLT-TORSION-PSISQ-DICTIONARY` — closed in the methodology probe for every natural index. The
   branch-free homogeneous relation, denominator-free relation, exact x-coordinate consequence,
   and detector are connected through a kernel-clean projective Kummer induction.
4. `FLT-TORSION-PRIME-TO-CHAR-FINITE` — closed in the methodology probe.
5. `FLT-TORSION-ALL-CHAR-FINITE` — closed in the methodology probe by algebraic-closure root
   existence and nonzero projective representatives; no finite-morphism scaffold is needed.
6. `FLT-TORSION-ETALE-COUNT` — open: when `(n : k) ≠ 0` and `k` is separably closed, prove the
   kernel has exactly `n ^ 2` rational points, including the bridge to the affine point type.
7. Migrate the two provider declarations and audit every exported consumer, especially
   `n_torsion_dimension`, `Module.Finite`, and `WeierstrassCurve.galoisRep`.

## Stop-loss rules

- Do not treat polynomial degree alone as a proof that its roots are precisely torsion points.
- Do not infer the all-characteristic theorem from `ΨSq_ne_zero`; its hypothesis is intentionally
  unavailable when the characteristic divides `n`.
- Do not count distinct x-roots as points. The y-fibres and the multiplicities built into `ΨSq`
  matter.
- Do not substitute a scheme-theoretic kernel without proving that its rational points agree with
  the repository's affine point kernel.
- Provider migration remains a separate task because the frozen source explicitly requests
  coordination with Kevin Buzzard and David Angdinata.

## Next exact theorem

The division-polynomial/Kummer lane and all-characteristic finiteness theorem are complete in the
methodology tree. The next bounded mathematical obligation is the remaining frozen provider:

```lean
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card (E.nTorsion n) = n ^ 2
```

The existing detector proves finiteness but does not count roots or y-fibres with multiplicity. The
next design spike should identify the smallest source-faithful route from the now-proved exact
point/division-polynomial dictionary to the cardinality statement—most likely a separability and
root-count theorem for `ΨSqₙ` plus the controlled two-point y-fibres, or a finite-etale kernel bridge.
Provider migration remains separately authorized work.
