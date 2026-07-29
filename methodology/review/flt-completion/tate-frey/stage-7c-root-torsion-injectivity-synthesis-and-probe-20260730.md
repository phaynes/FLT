# Stage 7C — controller synthesis and executable root-separation probe

## Classification

This is controller-authored synthesis and local executable evidence, not an independent model
review and not proof promotion. It compares the two Stage 7 design arms and records a smaller
direct route discovered and checked while those arms ran.

## Decision

Both model arms converge on the same first fact: an affine prime-to-residue-characteristic torsion
point has coordinates in the valuation subring. They diverge after that:

- Stage 7B recommends proving a weak subtraction-compatibility or full additivity lemma.
- Stage 7A recommends a homomorphism-free division-polynomial multiplicity argument.
- The controller probe found a smaller homomorphism-free route: split `ΨSq` into its actual
  squarefree factors and apply a generic separable-root reduction lemma factor by factor.

The selected implementation route is the third route. It avoids constructing an additive
specialization map and avoids the heavier root-multiplicity accounting proposed by Stage 7A.

## Executable probe

- Scratch source: `/tmp/flt-root-separation.FVrOEB/Probe.lean`
- SHA-256: `a93ac0f385690c53963fbab8014c8c111f2e316acbbb1ffc651b7511c1c1cb1f`
- Size at the recorded audit: `292` lines
- Command: `lake env lean /tmp/flt-root-separation.FVrOEB/Probe.lean`
- Result: direct elaboration passed.

The scratch source deliberately imports `GoodReduction.lean`; it is evidence and a builder aid,
not a file to copy into the source tree unchanged. Production code must be split so imports remain
acyclic.

The following proof shapes compiled:

1. two roots of a polynomial over a domain are equal when their residue images agree and the
   residue polynomial is separable;
2. the same result for two pointwise-coprime separable factors;
3. a root of a unit-leading-coefficient polynomial over an integrally closed fraction ring lifts
   to the base ring;
4. projective residue of a primitive integral vector is coordinatewise residue;
5. equality of reductions of two integral affine triples gives equality of their residue `x` and
   `y` coordinates;
6. the `y` coordinate is integral once `x` is integral, using the monic Weierstrass equation;
7. `Ψ₂Sq(x) = (2y + a₁x + a₃)^2` on a point of the curve;
8. an affine `n`-torsion point has integral `x` and `y` coordinates;
9. specialization of integral affine and zero points has the expected explicit projective class.

Every audited probe declaration depended on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No probe declaration depended on `sorryAx`, a custom axiom, completion, Henselianity, oddness,
residue characteristic exclusions, or a target-equivalent assumption.

## Direct injectivity assembly

For two torsion points with equal specialization:

1. Zero/affine cases are separated by projective `Z=0` versus `Z=1`.
2. Affine points have integral coordinates, so equal specializations give equal reduced `x` and
   `y` coordinates.
3. The exact torsion dictionary gives a root of `ΨSq`; `ΨSq_ofNat` classifies its `x` coordinate
   as a root of `preΨ' n`, or, for even `n`, a root of `Ψ₂Sq`.
4. `prePsi_separable`, `psiTwoSq_separable`, and `prePsi_pointwise_coprime` on the reduced curve,
   combined with the generic root-reduction lemma, force the two integral `x` coordinates to be
   equal. For odd `n` only `preΨ' n` is used; characteristic two therefore remains supported.
5. `eq_or_eq_neg_of_xRep_eq_xRep` gives equality or the negation case.
6. In the negation case, equal reduced `y` coordinates make the reduced negation gap zero, hence
   the reduced `x` is a root of `Ψ₂Sq`.
7. If the source `x` came from `preΨ' n`, pointwise coprimality gives a contradiction. If it came
   from `Ψ₂Sq`, the exact dictionary at `2` shows the source point is self-negative, so the two
   points were equal.

This covers the point at infinity, even `n`, residue characteristics two and three, and arbitrary
possibly noncomplete valuation subrings without introducing extra assumptions.

## Remaining risk

The generic bricks and integral-coordinate tranche are executable. The complete specialization
case assembly has not yet elaborated as one theorem. Therefore the obligation remains open and no
graph or Helios promotion is authorized by this report.

## Build order

1. Port the generic polynomial/integral-root bricks into an acyclic source module.
2. Add specialization-facing coordinate lemmas to `GoodReduction.lean` or an acyclic helper.
3. Compile and axiom-audit this tranche before attempting the full `InjOn` proof.
4. Assemble `pointSpecialization_injOn_torsion` and replace the original target `sorry` only when
   the unchanged theorem builds and audits cleanly.
5. Run narrow, FLT, FLTMethodology, umbrella, prohibited-token, and independent-review gates.

