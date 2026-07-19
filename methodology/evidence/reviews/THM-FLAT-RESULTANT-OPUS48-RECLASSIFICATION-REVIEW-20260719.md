# THM-FLAT-RESULTANT independent reclassification review

## Identity and scope

- Reviewer model: `claude-opus-4-8`
- Mode: read-only
- Reviewed change: source mapping, dependency correction, completion accounting, and deferred proof
  design for `WeierstrassCurve.resultant_Φ_ΨSq`
- Source PDF SHA-256: `5b738265ea3a454721166cc0787426786cdd5292d67bc25dcd3ba46d37c06799`

## Verdict

**PASS — bounded control reclassification.**

## Source adjudication

The reviewer inspected SRC-027 Theorem 1.1, the characteristic/specialization discussion, and §8
identity (43). The general Tate-form identity is an integral universal-polynomial identity over
`ℤ[a₁,a₂,a₃,a₄,a₆]`, so it specializes to arbitrary commutative rings. SRC-027 therefore gives exact
mathematical coverage while leaving honest formal gaps:

- Schmidt's multiplication-polynomial normalization must be identified with Mathlib `Φ/ΨSq`;
- the source's natural `n ≥ 2` result must be connected to integer indices and the `±1` cases;
- universal specialization and padded-resultant conventions require Lean adapters; and
- the external theorem cannot be introduced as a custom T1 axiom.

## Dependency adjudication

The reviewer confirmed independence at three levels:

1. Textually, `isCoprime_Φ_ΨSq` does not invoke `resultant_Φ_ΨSq`.
2. Kernel-level, the fresh recorded audit for `isCoprime_Φ_ΨSq` contains only `propext`,
   `Classical.choice`, and `Quot.sound`; it has no `sorryAx` inherited from the resultant.
3. Mathematically, `torsion_flat_of_good_reduction` needs coprimality plus the finite-flat
   group-scheme/Hopf-algebra construction and local/global torsion transport. The exact resultant
   power supplies neither missing bridge.

## Completion accounting

The required theorem denominator may legitimately change from **13 to 12**. The programme's T1/T3
terminal policy is defined by the exported theorem's dependency/axiom closure, not repository-wide
elimination of every unrelated `sorry`. The optional resultant remains visibly `admitted` and
`unreviewed`; it is neither deleted nor falsely counted as proved.

The following changes are therefore approved:

- `required_for_completion = false`;
- `critical_path = false`;
- `unlocks = 0`; and
- removal of `THM-FLAT-RESULTANT` from `THM-FLAT-GOOD-REDUCTION.dependencies`.

No proof or review state was advanced.

## Design feedback incorporated

- The true first crux is the Schmidt-to-Mathlib `A_n^T/B_n^T` versus `Φ/ΨSq` convention adapter.
- Because the Lean target permits either sign, Schmidt's §2 and §8 arithmetic route can avoid the
  full Fourier calculation used for the exact positive sign. This is the preferred R1 candidate.
- The stale `DivisionPolynomialCoprimeAudit.lean` prose claiming a remaining resultant dependency
  was corrected; the executable audit itself was already truthful.

## Non-closure statement

This PASS does not prove FLT, `resultant_Φ_ΨSq`, `torsion_flat_of_good_reduction`, or
`FLT-TATE-FLAT`. The optional admitted declaration remains an explicit cleanup item.

## Recommended next critical-path task

Proceed to a bounded design/build cycle for the source-unblocked
`THM-TAME-FIXED-FIELD-UNIFORMIZER`, beginning with the fixed-field/value-group bridge rather than
attempting the final theorem in one step.
