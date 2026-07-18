# GPT-5.6 xhigh independent review — p-adic-Hodge G1 synthesis

Verdict: **REVISE-SUBSTANTIVE**.

The proposed bounded constructions are kernel-sound after mechanical import repair, but the
synthesis is not persistence-safe as written. No p-adic-Hodge provider or graph node is promoted.

## Kernel replay

The independent reviewer replayed the two disposable probe groups. All thirteen candidate
declarations audited exactly to:

```text
[propext, Classical.choice, Quot.sound]
```

The stated import `Mathlib.RingTheory.DedekindDomain.Ideal` does not exist. The verified imports are:

```lean
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dimension.Finrank
```

With those imports, Blocks A--D compile in the proposed namespace and universes.

## Findings

1. The guarded `IsPlaceAbove` construction is sound. The unguarded predicate is vacuous at
   `ell = 0`; `[Fact ell.Prime]` excludes that case. The reviewer additionally proved both
   directions between `IsPlaceAbove ell v` and residue characteristic `ell`.
2. The explicit diagonal tensor action and invariant submodule are correct. Both scalar-commutation
   hypotheses are load-bearing, and no global tensor-product group-action instance is introduced.
3. `IsCrystallineRelQp` is misleading for an arbitrary supplied ring. Rename it exactly to
   `PeriodInvariantFinrankMatchesQp` and state explicitly that it is only a generalized finrank
   equality, not crystallinity, `D_cris`, `IsCrystallineAt`, or a comparison theorem.
4. `xi`, not `t`, generates `ker theta`; `t = log [epsilon]`. The fixed-scalar theorem and ramified
   coefficient transport remain separate providers. The statement about convergence of `t` and the
   claim that inverting `t` automatically inverts `p` require correction or explicit theorems.
5. N-Cp and N-PD remain genuinely separate. The graph must additionally expose a place-compatible
   `Q_p -> K_v` bridge; `Field.absoluteGaloisGroup.map` is not itself the claimed bundled injection.
   The PD-envelope ordering also depends on whether a generator of `ker theta` is used.
6. Mathlib already provides `spectralNorm_eq_of_equiv` and a weak universal divided-power algebra;
   neither closes the missing continuous-completion action or ideal PD envelope, but both must be
   recorded as reusable infrastructure.

## Corrected bounded candidate

The safe candidate, after the naming/import/docstring correction, contains thirteen declarations:

1. `unguarded_natCast_mem_of_zero`;
2. `IsPlaceAbove`;
3. `IsPlaceAbove.natCast_ne_zero`;
4. `IsPlaceAbove.unique`;
5. `exists_prime_natCast_mem`;
6. `diagTensorAut`;
7. `diagTensorAut_tmul`;
8. `diagTensorRep`;
9. `diagTensorAut_smul_left`;
10. `periodSubmodule`;
11. `mem_periodSubmodule`;
12. `periodSubmodule_eq_top`;
13. `PeriodInvariantFinrankMatchesQp`.

The first residual construction is a `MulSemiringAction` of the absolute Galois group of `Q_p` on
`C_p`, followed separately by continuity and the place-compatible local-field embedding. The full
`FLT-MLT-PADIC-HODGE` obligation remains a definition gap.
