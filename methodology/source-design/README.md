# FLT-205 source-design register

Task: `task:fg-flt-ra-math-source-design-20260716`

This directory is the mathematical definition-of-ready gate between the frozen component BOM and
provider implementation. A component is `READY` only when all seven evidence fields below are
complete for every obligation it owns:

1. exact primary source and locator;
2. source-to-Lean hypothesis translation;
3. proof architecture;
4. acyclic sublemma graph;
5. counterexample and false-weakening review;
6. pinned-library matches and negative searches; and
7. an elaborating Lean signature with a standard-axiom audit.

The machine-readable authority is `methodology/control/source-design.ndjson`. A `BLOCKED` or
`PARTIAL` row is progress evidence, not permission to start a provider and not proof completion.
The seven existing-contract rows are ready because they contain no new mathematical provider: they
are exact definitions or elementary adapters already audited in FLT-204.

## Current frontier

- `existing-*`: 7 `READY` contract/adapter components.
- `brauer-nesbitt`: `PARTIAL`; exact signature, counterexamples, library survey, and the
  finite-joint-image reduction are kernel-clean. The exact primary-source theorem and the finite
  algebra terminal remain open.
- `mazur`: `PARTIAL`; Serre's exact Frey irreducibility proposition, its character-dichotomy source,
  and Mazur's torsion theorem are pinned to primary pages. Semistability, the non-vacuous finite
  torsion bound, full two-torsion, the exact line/quotient character dichotomy, and the terminal
  `4p > 16` contradiction are now signature-green. The concrete Frey full-two-torsion provider is
  additionally kernel-clean: all two-torsion points are explicitly classified and shown distinct.
  The concrete Frey semistability provider is also kernel-clean: explicit `c₄` and discriminant
  unit arguments give good or multiplicative reduction at every rational prime. The concrete
  character theorem and quotient-isogeny geometry remain open.
- `quaternion-boundary`: `PARTIAL`; the upstream norm-one injection has been rejected and replaced
  by the correct order-unit quotient route from Voight Lemma 26.5.1. Existing adelic cocompactness
  is reusable, but compact-open-to-order and quotient-injection bridges remain open.
- `modularity-lifting`: `PARTIAL`; Taylor 2018 is selected and source hypotheses are reviewed, but
  the honest source signature cannot elaborate until coefficient, p-adic Hodge, and RACAR
  vocabulary exists.
- `coefficients`: `PARTIAL`; provisional residual relations elaborate, but lattice existence,
  semisimplification, and uniqueness remain open.
- `tate-frey`: `PARTIAL`; the downstream signatures and several support reductions are known. The
  formal Euler-product/q-expansion identity, substitution-evaluation bridge, and concrete
  Tate-parameter round trip, and split-multiplicative reduction of the explicit Tate curve are now
  kernel-clean in methodology probes. The exact local-form boundary is also signature-green and
  reduces to equal-`j` quadratic-form classification plus exclusion of a second split quadratic
  twist. The general `tateEquiv` integration is now proved to be a mechanical composition of the
  explicit Tate-curve equivalence and that variable change. Those two local source theorems, the
  explicit `tateCurveEquiv` construction, provider migration, and the remaining geometric
  construction families are open.
- all remaining components: `BLOCKED` at this global gate until their own complete packet exists.

This deliberately prevents a single attractive theorem from authorizing downstream construction
while another obligation owned by the same scheduling envelope is still source-ambiguous.
