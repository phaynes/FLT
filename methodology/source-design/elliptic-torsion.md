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

theorem n_torsion_finite_of_psiSq_detection
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] {n : ℕ}
    (hn : (n : k) ≠ 0) (hdetect : PsiSqDetectsNTorsion E n) :
    Finite (E.nTorsion n)

theorem psiSqDetectsNTorsion_two
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 2

theorem psiSqDetectsNTorsion_three
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k] :
    PsiSqDetectsNTorsion E 3
```

The proof is elementary and standard-axiom clean. It bounds x-coordinates by roots of the detector
polynomial, then bounds each y-fibre by the roots of a nonzero monic quadratic. Thus the
characteristic-prime-to-`n` finiteness lane is reduced to the single exact dictionary proposition
`PsiSqDetectsNTorsion`.

The `n = 2` and `n = 3` cases are also kernel-clean. The first derives the fixed-point condition
under affine negation from `2 • P = 0`, expands `Ψ₂Sq`, and eliminates the Weierstrass equation. The
second passes through the nonvertical affine doubling formula, clears its tangent denominator, and
derives the `Ψ₃` equation. Together they confirm the detector interface's normalization and point
representation in both parity classes. They do not remove the open general recurrence.

This does not yet prove the frozen general finiteness theorem. When the characteristic divides
`n`, `ΨSq_ne_zero` is unavailable and the proof needs either a different nonzero detector or the
finite-morphism/group-scheme route.

## Minimal implementation graph

Build in this order:

1. `FLT-TORSION-Y-FIBER` — closed in the methodology probe: a fixed x-coordinate has finitely many
   affine y-coordinates.
2. `FLT-TORSION-DETECTOR-FINITE` — closed in the methodology probe: any nonzero x-coordinate
   detector makes `E[n](k)` finite.
3. `FLT-TORSION-PSISQ-DICTIONARY` — partial: the `n = 2` and `n = 3` cases are closed; prove the general
   `PsiSqDetectsNTorsion` statement from the affine group law and division-polynomial recurrences.
   A stronger x-coordinate multiplication formula is an acceptable provider if this theorem is an
   immediate corollary.
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

The next bounded theorem to attempt remains the general provider for:

```lean
FLTMethodology.Torsion.PsiSqDetectsNTorsion E n
```

The `n = 2` and `n = 3` cases are now proved. The first likely residual Lean goal for arbitrary `n` is the missing
induction theorem relating the binary-recursive affine `nsmul` implementation to the
division-polynomial recurrence. If that induction does not factor cleanly, first prove the stronger
point-coordinate formula and derive the detector theorem.
