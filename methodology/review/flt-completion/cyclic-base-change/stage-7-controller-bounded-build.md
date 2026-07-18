# Controller bounded build — cyclic-base-change repair vocabulary

Verdict: **KERNEL-GREEN — INDEPENDENT BUILD REVIEW REQUIRED**.

The reviewed second Fable repair has been materialised in the methodology-only module
`FLTMethodology/Probes/CyclicBaseChangeBoundary.lean`. The public theorem
`cyclic_base_change`, its endpoints, the proof graph, the T2 registry, and the `FLT-CBASE`
obligation state are unchanged.

The bounded module contains exactly:

- four proved structural lemmas: `even_finrank_of_even_base`,
  `mem_preimageComapFinset_iff`, `natCast_notMem_of_mem_preimageComapFinset`, and
  `heckeAlgebra_algHom_ext`;
- eight interface definitions in `FLTMethodology.CBaseRepair`, including the repaired conditional
  `BaseChangeFiberUpToTwistOfIrreducible` and the two explicit open analytic boundaries;
- the proved regression `not_isIrreducible_trivial_two_dim`, excluding the trivial
  two-dimensional representation from the repaired fiber antecedent.

Kernel gate:

```text
lake build FLTMethodology.Probes.CyclicBaseChangeBoundary
  -> Build completed successfully (3693 jobs)

All thirteen declarations depend exactly on:
  [propext, Classical.choice, Quot.sound]
```

The module contains no `sorry`, `admit`, `axiom`, `knownin1980s`, `unsafe`, or
`native_decide`. These declarations are infrastructure and checked vocabulary only. They do not
prove forward base change, descent, image characterization, cuspidality, Jacquet--Langlands,
multiplicity one, or conductor compatibility. `FLT-CBASE` therefore remains `admitted` and the
next gate is an independent Opus 4.8 build review of this exact bounded tranche.
