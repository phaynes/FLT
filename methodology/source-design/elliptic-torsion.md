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
dictionary. Degenerate equal-x and infinity branches still require explicit recurrence cases.
The corresponding bihomogeneous form is also kernel-clean, including its scaling law, symmetry,
affine specialization, and infinity specializations. Consequently recurrence algebra can now be
performed directly on representative pairs `[X,Z]`, without dividing by `Z` or losing the infinity
case.

The full `n = 0,1,2,3` base block and the first recursive even case `n = 4` are kernel-clean. The
first two cases are structural. The `n = 2`
case derives the fixed-point condition
under affine negation from `2 • P = 0`, expands `Ψ₂Sq`, and eliminates the Weierstrass equation. The
second passes through the nonvertical affine doubling formula, clears its tangent denominator, and
derives the `Ψ₃` equation. The `n = 4` proof then splits on whether the point is already two-torsion,
doubles the remaining case, and consumes the separately named `preΨ₄`/doubled-`ψ₂` identity. Together
they confirm the detector interface's normalization and point representation in both parity classes
and validate one recurrence-shaped step. They do not remove the open arbitrary-index recurrence.

This does not yet prove the frozen general finiteness theorem. When the characteristic divides
`n`, `ΨSq_ne_zero` is unavailable and the proof needs either a different nonzero detector or the
finite-morphism/group-scheme route.

## Minimal implementation graph

Build in this order:

1. `FLT-TORSION-Y-FIBER` — closed in the methodology probe: a fixed x-coordinate has finitely many
   affine y-coordinates.
2. `FLT-TORSION-DETECTOR-FINITE` — closed in the methodology probe: any nonzero x-coordinate
   detector makes `E[n](k)` finite.
3. `FLT-TORSION-PSISQ-DICTIONARY` — partial: the full detector block `n = 0,1,2,3,4` is closed. The
   branch-free `DivisionPolynomialXHomogeneous` is equivalent to the denominator-free relation,
   which implies both the exact x-coordinate formula and detector and is proved for `n = 0,1,2`.
   Prove the homogeneous relation for arbitrary `n` from the affine group law and
   division-polynomial recurrences. The distinct-x differential-addition/Kummer
   component needed by the adjacent-pair induction is closed; add the degenerate branch lemmas and
   polynomial recurrence normalization. Its bihomogeneous scaling and infinity laws are closed.
4. `FLT-TORSION-PRIME-TO-CHAR-FINITE` — assembly is already closed; instantiate step 3.
5. `FLT-TORSION-ALL-CHAR-FINITE` — open: cover the characteristic-dividing case without assuming
   `ΨSq n ≠ 0`, or introduce and connect a source-faithful finite multiplication morphism.
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

The next bounded theorem to attempt is the general provider for:

```lean
FLTMethodology.Torsion.DivisionPolynomialXHomogeneous E n
```

Its equivalence to the match-based relation, that relation's `n = 0,1,2` cases, and its implications
to `DivisionPolynomialXFormula` and `PsiSqDetectsNTorsion` are now proved. The first likely residual
Lean goal is a recurrence step
for an adjacent pair of multiples, consuming `addX_mul_addNegX_kummer` in the distinct-x branch and
the existing doubling/vertical lemmas in the equal-x branch. The polynomial side must normalize the
resulting `kummerBiquadratic` expression to Mathlib's odd/even `preΨ`, `ΨSq`, and `Φ` recurrences.
