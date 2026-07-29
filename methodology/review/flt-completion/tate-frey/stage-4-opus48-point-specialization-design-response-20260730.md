# Stage 4 — Opus 4.8 point-specialization design response

## Verdict

`IMPLEMENTABLE-AFTER-NAMED-PREFIX`

The unchanged theorem `WeierstrassCurve.torsion_unramified_of_good_reduction` is mathematically
sound at its current generality, but the pinned libraries do not contain the point-specialization
and prime-to-residue-characteristic injectivity package needed to prove it. The smallest sufficient
prefix is:

1. a specialization map from `(E⁄ksep).Point` to a full reduced projective point;
2. inertia invariance of that map;
3. injectivity of that map on `n`-torsion.

Once those three declarations are proved, the existing
`WeierstrassCurve.torsion_fixed_of_invariant_injective` closes the target by direct application.

This is a design result only. It does not prove the target or authorize graph promotion.

## Execution and fallback

The scheduled Fable 5 design call failed operationally with an Anthropic `529 Overloaded` response
before returning a mathematical verdict. Under the configured fallback policy, Opus 4.8 performed
the read-only design.

- designer: `opus48-primary-designer-d8`
- model: `claude-opus-4-8`
- Claude session: `f440718c-e710-4405-a14d-320cc14cd68d`
- transcript:
  `/Users/philiphaynes/.claude/projects/-Volumes-second-store-devel-proof-forks-FLT-good-reduction-specialization-20260730/f440718c-e710-4405-a14d-320cc14cd68d.jsonl`
- model duration: `800,290 ms`
- requests: `50`
- input tokens: `91`
- cache-creation input tokens: `260,355`
- cache-read input tokens: `2,709,892`
- output tokens: `120,358`

The two exploratory child calls attempted by Opus also received `529 Overloaded`; Opus completed
the audit using direct repository reads. Their failures do not constitute a mathematical finding.

## Route audit

### Accepted for the next bounded tranche

Normalized integral projective coordinates followed by residue reduction is the smallest plausible
construction of the specialization map and its inertia invariance:

- normalize a nonzero representative in `ksep^3` to coordinates in the valuation subring with at
  least one unit coordinate;
- reduce the coordinates to the residue field, where the unit coordinate remains nonzero;
- prove the reduced coordinates satisfy the coefficient-reduced Weierstrass equation;
- prove independence from the choice of normalized representative;
- use `ValuationSubring.inertia_residue_smul_eq` for inertia invariance.

The first real build tranche must prove reusable normalization/reduction declarations. Merely adding
the three missing fields as `sorry` stubs is not proof progress and is prohibited by the controller.

### Accepted only as a later injectivity route

The existing `WeierstrassCurve.isCoprime_Φ_ΨSq` and Mathlib division-polynomial degree/leading
coefficient results are relevant to injectivity, but two missing leaves must be made explicit:

- a checked dictionary between `n • P = 0` for `WeierstrassCurve.Affine.Point` and vanishing of the
  division polynomial at the point's coordinate;
- sufficient separability/discriminant control after reduction to rule out collisions.

The vendored Hasse–Weil slice contains related division-polynomial results, but its point type is
different and no checked equivalence to the target's `Affine.Point` has yet been proved.

### Rejected for this bounded milestone

- A generic scheme-theoretic properness/finite-etale construction is not a bounded substitute: the
  pinned target has no checked bridge between the concrete Weierstrass point API and such a torsion
  scheme.
- The cached AINTLIB `TorsionUnramifiedFibre` development is not a clean provider for this theorem.
  It is outside the FLT import path and depends on admitted scheme-theoretic results.
- A reduction codomain containing only the `x` coordinate is insufficient because `P` and `-P`
  ordinarily have the same `x` coordinate.

## Dependency order

```text
proved baseRingHom/locality/compatibility
        |
        v
integral unit-coordinate normalization
        |
        v
well-defined projective residue specialization
        |
        +----> inertia invariance
        |
        v
prime-to-residue-characteristic torsion injectivity
        |
        v
torsion_fixed_of_invariant_injective
        |
        v
torsion_unramified_of_good_reduction
```

## Objective gates

For each claimed leaf:

- direct elaboration and the narrow good-reduction build must pass;
- `lake -H build FLT FLTMethodology` must pass at the frozen dependency state;
- `#print axioms` must contain no `sorryAx` and no new axiom;
- no target or graph state may be promoted solely because a typed interface elaborates.

## Stop-loss boundary

If normalization and honest projective residue reduction cannot be completed within the next
bounded build, preserve any kernel-clean generic lemmas and reclassify the remaining work precisely.
If the later torsion dictionary or separability leaf cannot be supplied, split it into a standalone
library obligation. Do not replace either leaf with an assumption, an opaque contract, or a theorem
equivalent to the target.

