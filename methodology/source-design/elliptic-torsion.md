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

theorem psiSq_eval_eq_zero_iff_nsmul_eq_zero ... :
    (E.ΨSq (n : ℤ)).eval x = 0 ↔
      (n : ℤ) • (Point.some x y h : (E⁄k).Point) = 0

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

`FLTMethodology/Probes/PsiSqExactDetection.lean` also proves the missing converse. At a root of
`ΨSqₙ`, representative nonzeroness forces `Φₙ` to be nonzero; the homogeneous relation then forces
the scalar multiple's second Kummer coordinate to vanish, hence the multiple is infinity. Thus for
every affine point the following equivalence is kernel-clean:

```lean
(E.ΨSq (n : ℤ)).eval x = 0 ↔
  (n : ℤ) • (Point.some x y h : (E⁄k).Point) = 0
```

Consequently the remaining cardinality gap is not an endpoint or dictionary problem. It is the
precise separability/multiplicity calculation matching the degree `n ^ 2 - 1` of `ΨSqₙ` to the
nonzero points, including the two-point `P`/`-P` fibres and the one-point two-torsion fibres.

`FLTMethodology/Probes/TorsionCardAssembly.lean` makes that boundary executable. It constructs an
equivalence between `E.nTorsion n` and infinity plus the affine zero locus

```lean
{(x,y) | (E.ΨSq n).eval x = 0 ∧ E.toAffine.Equation x y}
```

and proves that the named contract `PsiSqAffineZeroCard E n`, asserting that this locus has
cardinality `n ^ 2 - 1`, implies the frozen `n_torsion_card` conclusion. Thus endpoint assembly,
the infinity contribution, and the final natural-number arithmetic are already kernel-clean.

`FLTMethodology/Probes/TorsionFiberCount.lean` decomposes the remaining locus into the exact finite
sum

```lean
∑ x : (E.ΨSq n).rootSet k, Nat.card (curveYFiber E x).
```

The root-index equivalence, finiteness of the root type and every quadratic y-fibre, the sum formula,
and a uniform-fibre specialization are kernel-clean. This makes the odd lane a root-count plus a
uniform two-point fibre proof. The even lane must partition the root set between `preΨₙ` and
`Ψ₂Sq`, charge two points to the former and one to the latter, and prove disjointness.

`FLTMethodology/Probes/TorsionParityCount.lean` now proves the exact root-set decomposition used by
those two lanes. For odd `n`, the roots of `ΨSqₙ` are exactly the roots of `preΨ'ₙ`. For even `n`,
they are exactly the union of the `preΨ'ₙ` roots and the `Ψ₂Sq` roots. It also proves that a
separable curve y-fibre has exactly two points over a separably closed field and that separability
of `preΨ'ₙ` converts its existing degree theorem into the required distinct-root count. The
`Ψ₂Sq` branch is now closed too: its cubic discriminant is nonzero, so it is separable and has
exactly three roots over a separably closed field; its vanishing is exactly the zero discriminant
of the quadratic in y, whose unique root is `-(a₁x+a₃)/2` when 2 is nonzero. The hard remainder is
therefore separability of `preΨ'ₙ` and its even-case coprimality with `Ψ₂Sq`, not the parity split or
fibre/cardinality plumbing.

The complementary fibre lemma is also closed: whenever `Ψ₂Sq(x)` is nonzero, an explicit Bezout
identity between the quadratic fibre polynomial and its derivative proves that the fibre polynomial
is separable. Consequently every `preΨ'ₙ` root outside the `Ψ₂Sq` roots automatically has the
required two-point y-fibre. No separate fibre-separability assumption remains.

The endpoint assembly is now closed as well. The kernel-clean theorem
`psiSqAffineZeroCard_of_prePsi_separable_coprime` proves `PsiSqAffineZeroCard E n` from precisely:

```lean
(E.preΨ' n).Separable
∀ x, (E.preΨ' n).eval x = 0 → E.Ψ₂Sq.eval x ≠ 0
```

This pointwise formulation is intentional. It remains meaningful when characteristic two makes a
root-set formulation vacuous, while the even branch derives `2 ≠ 0` from `(n : k) ≠ 0`. Thus all
parity, fibre, distinct-root, union-sum, and natural-number arithmetic obligations are discharged;
only the two division-polynomial hypotheses above remain.

`FLTMethodology/Probes/PrePsiTwoTorsion.lean` now narrows the coprimality hypothesis further in the
even lane. At a root `x` of `Ψ₂Sq`, with `2 ≠ 0`, it proves

```lean
(preΨ₄(x))² = -4 * (Ψ₃(x))³
(Ψ₂Sq'(x))² = -16 * Ψ₃(x)
Ψ₃(x) ≠ 0
preΨ₄(x) ≠ 0
preΨ'ₙ(x) = preNormEDS' 0 (Ψ₃(x)) (preΨ₄(x)) n.
```

Thus the residual even-case coprimality theorem is no longer a curve-coordinate calculation. It is
the abstract closed nonvanishing formula for `preNormEDS' 0 c d n` when `c ≠ 0`, `d ≠ 0`,
`d² = -4c³`, and `(n : k) ≠ 0`. Computation supports the standard formula: odd terms are signed
powers of `c`; terms congruent to two modulo four are `(n/2)` times a power of `c`; terms divisible
by four are `(n/4)` times a power of `c` times `d`.

That target is now proved in `FLTMethodology/Probes/SpecialPreNormEDS.lean`. After the
parameterization `c = -t²`, `d = -2t³`, the simultaneous kernel-clean formula is

```lean
preNormEDS' 0 (-t²) (-2t³) (2r+1) = (-1)^r * t^(r(r+1))
preNormEDS' 0 (-t²) (-2t³) (2(r+1)) = (-1)^(r+2) * (r+1) * t^(r(r+2)).
```

The relation `d² = -4c³`, together with `2 ≠ 0` and `c ≠ 0`, supplies this parameter directly as
`t = d/(2c)`. Hence a nonzero even index makes every factor in the second formula nonzero.

The odd coprimality lane is now closed independently of that formula, including characteristic two.
After base change to an algebraic closure, a common root of `preΨ'ₙ` and `Ψ₂Sq` supplies an affine
point killed by both `n` and `2`. Oddness makes those scalars coprime, so the point would be zero,
contradicting its affine constructor. The kernel-clean
`prePsi_pointwise_coprime_of_even_preNormEDS` therefore reduces all pointwise coprimality to the
even-index part of the specialized recurrence only. That part is now discharged by
`specialEvenPreNormEDS_ne_zero`, so `prePsi_pointwise_coprime` is unconditional. The endpoints
`psiSqAffineZeroCard_of_prePsi_separable` and `n_torsion_card_of_prePsi_separable` assemble the exact
affine and full torsion counts from separability of `preΨ'` alone.

## Dual-number reduction of the separability input

`FLTMethodology/Probes/DualTangent.lean` now proves the first-order algebra directly over Mathlib's
`DualNumber k`. For every polynomial `p`, evaluation at `x + ε dx` is kernel-cleanly identified as

```text
p(x + ε dx) = p(x) + ε * p'(x) * dx.
```

The same module expands the mapped Weierstrass equation and proves that a dual point lies on the
curve exactly when its base point lies on the curve and its infinitesimal coordinates obey

```text
W_X(x,y) * dx + W_Y(x,y) * dy = 0.
```

At a root of `preΨ' n`, the proved coprimality with `Ψ₂Sq` makes `W_Y(x,y)` nonzero. Therefore a
chosen nonzero `dx` has a unique completing `dy`. `PrePsiInfinitesimal.lean` assembles these facts:
a hypothetical common root of `preΨ' n` and its derivative produces a concrete nonconstant
dual-number point on the mapped curve at which the mapped `preΨ' n` also vanishes. Over an
algebraically closed field, excluding these witnesses implies separability.

This closes the polynomial and tangent bookkeeping, but not yet the mathematical terminal. The
smallest remaining interface must identify that dual division-polynomial zero with an
infinitesimal element of the kernel of multiplication by `n`, then prove that the tangent map of
`[n]` is multiplication by `(n : k)`. Its injectivity when `(n : k) ≠ 0` excludes the witness. The
pinned library has no group law over dual numbers and no invariant-differential/formal-group API,
so that bridge must be implemented explicitly or replaced by a sourced finite-etale component.

## Formal-group component split

`FLTMethodology/Probes/FormalGroupLinearization.lean` now closes the reusable algebraic half for
every one-dimensional formal group over a commutative ring. It defines the formal `n`-series and
proves that its constant coefficient is zero and its linear coefficient is exactly `(n : R)`.
Therefore, when `(n : R) ≠ 0`, the `n`-series is already nonzero at first order. These declarations
have only the standard axiom trio.

`FLTMethodology/Probes/PrePsiFormalGroupAdapter.lean` freezes the exact remaining dependency as
`PrePsiFormalGroupAdapter E n`. The adapter owns three pieces of elliptic information:

1. a local formal group and tangent coordinate at the identity;
2. preservation of the nonzero tangent direction after translating the explicit witness to the
   identity; and
3. the fact that the witness lies in the infinitesimal kernel of `[n]`, expressed by annihilation
   of that tangent coordinate by the formal `n`-series.

Given the adapter, `isEmpty_prePsiInfinitesimalWitness_of_formalGroupAdapter` excludes every
witness when `(n : k) ≠ 0`, and `prePsi_separable_of_formalGroupAdapter` proves the required
separability. Both assembly results are kernel-clean. The adapter itself is deliberately not
postulated or instantiated: the next mathematical work is to construct the elliptic formal group
(for example from the local parameter `-x/y` at infinity), prove the translation/tangent
nonzeroness lemma, and connect the dual division-polynomial zero to formal multiplication. Thus no
separability or torsion-cardinality completion is claimed yet.

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
6. `FLT-TORSION-PARITY-COUNT` — partial: all parity, fibre, cardinality, coprimality, local
   dual-number tangent work, and generic formal-group linearization are closed. Construct the
   concrete `PrePsiFormalGroupAdapter` to exclude the explicit infinitesimal witness and hence
   prove `preΨ'` separable.
7. `FLT-TORSION-ETALE-COUNT` — reduced: the exact affine count follows mechanically from those two
   hypotheses, and its bridge to `Nat.card (E.nTorsion n) = n ^ 2` is closed. A finite-etale proof
   may instead be used to discharge the same two mathematical facts.
8. Migrate the two provider declarations and audit every exported consumer, especially
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

The next exact theorem is now:

```lean
theorem psiSqAffineZeroCard
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] [IsSepClosed k]
    {n : ℕ} (hn : (n : k) ≠ 0) : PsiSqAffineZeroCard E n
```

The root-set parity split, splitting-to-root-count adapter, both fibre multiplicities, and the final
odd/even sum arithmetic are now proved. The exact conditional assembly theorem needs only
square-freeness of `preΨₙ` and pointwise coprimality with `Ψ₂Sq`; the even coprimality lane is now
closed by the specialized EDS formula described above, while the odd lane is closed in every
characteristic. The exact conditional full torsion-card theorem now depends only on separability.
The dual-number construction has reduced that input to excluding a concrete infinitesimal kernel
witness via the differential of multiplication by `n`. The generic formal-group differential is
now proved and the exact remaining elliptic dependency is frozen as `PrePsiFormalGroupAdapter`;
constructing that adapter is the next theorem-building step. A finite-etale kernel bridge remains
the alternative route to the same fact. Provider migration remains separately authorized work.
