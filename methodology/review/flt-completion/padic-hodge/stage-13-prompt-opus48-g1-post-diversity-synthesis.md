# Opus 4.8 post-diversity synthesis — p-adic-Hodge G1 infrastructure

Act as the primary post-diversity synthesizer at difficulty 10. Work read-only in
`/Volumes/second-store/devel/proof-forks/FLT` at commit `c6c1a7d`. Do not edit repository files, task
state, graph rows, source registers, or Lean sources. Temporary Lean probes outside the repository
are allowed.

Read in full:

- `methodology/review/flt-completion/padic-hodge/stage-9-opus48-g1-crystalline-design.md`;
- `methodology/review/flt-completion/padic-hodge/stage-11-gpt56xhigh-g1-decomposition-review.md`;
- `methodology/review/flt-completion/padic-hodge/stage-12-fable5-g1-diversity-repair.md`;
- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`;
- every cited pinned Mathlib/FLT API and the current control rows for `FLT-MLT-PADIC-HODGE`.

Synthesize one exact, source-honest design that reconciles all three stages. In particular:

1. Give the smallest bankable period-functor slice with exact Lean declarations, imports,
   namespaces, universes, typeclass assumptions, and dependency order.
2. Re-probe the guarded `IsPlaceAbove` predicate, non-vacuity/uniqueness/existence results, explicit
   diagonal tensor representation, semilinearity, invariant submodule, and Qp-relative dimension
   predicate. Reject any global `SMul Gamma (B tensor[E] V)` instance or left-factor action diamond.
3. Decide whether `IsCrystallineRelQp` is safe to bank as vocabulary or is still mathematically too
   suggestive. It must not be described as `IsCrystallineAt` or a comparison theorem.
4. Specify exact new provider nodes for the continuous Galois action on `C_p` and for PD envelopes,
   including dependencies, difficulty, owners, completion gates, and first residual Lean goals.
5. Keep `xi` as the generator of `ker theta`; keep `t = log [epsilon]` in its correct role. Keep
   `B_cris^Gamma = K_0` as a theorem provider, never a structure field or assumed scalar identity.
6. Separate the Qp-first coefficient architecture from the deferred finite-coefficient
   `K_0 tensor[Qp] E` module. Do not balance `B_cris` over arbitrary ramified `E`.
7. Re-run every proposed bankable declaration in disposable Lean probes and audit it to exactly
   `[propext, Classical.choice, Quot.sound]`.

Return exactly one verdict: `READY-FOR-GPT-REVIEW`, `REVISE`, `DECOMPOSE-FURTHER`, `OBSTRUCTION`, or
`NO-RESULT`. Give the exact production slice, exact provider rows/edges proposed for later review,
all stop-losses, and the first genuine residual Lean goal. This synthesis authorizes no production
build, graph mutation, `IsCrystallineAt` theorem, comparison theorem, T2 assumption, or obligation
promotion; an independent GPT review remains mandatory.
