# GPT-5.6 xhigh independent review — p-adic-Hodge G1 post-diversity synthesis

Act as the independent mathematical, Lean, and graph reviewer at difficulty 10. Work read-only in
`/Volumes/second-store/devel/proof-forks/FLT`. Review the immutable source state at commit
`dca95b766b94651010f3859b747e0ee19f046abc`; do not edit repository files, task state, graph rows,
source registers, or Lean sources. Temporary Lean probes outside the repository are allowed.

Read in full:

- `methodology/review/flt-completion/padic-hodge/stage-9-opus48-g1-crystalline-design.md`;
- `methodology/review/flt-completion/padic-hodge/stage-11-gpt56xhigh-g1-decomposition-review.md`;
- `methodology/review/flt-completion/padic-hodge/stage-12-fable5-g1-diversity-repair.md`;
- `methodology/review/flt-completion/padic-hodge/stage-13-opus48-g1-post-diversity-synthesis.md`;
- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`;
- every cited pinned Mathlib/FLT declaration and the live `FLT-MLT-PADIC-HODGE` control rows.

Independently adjudicate all of the following:

1. Replay the exact proposed Blocks A--D in disposable Lean files with their stated imports,
   universes and typeclass hypotheses. Audit every declaration proposed for persistence to exactly
   `[propext, Classical.choice, Quot.sound]`.
2. Verify the guarded `IsPlaceAbove` predicate and all claimed non-vacuity, uniqueness and existence
   theorems. Test edge cases including `ell = 0`, residue characteristic, coprimality and every
   `HeightOneSpectrum` coercion.
3. Verify `diagTensorAut`, `diagTensorRep`, semilinearity and invariant-submodule scalar closure.
   Confirm that no global/scoped `SMul Gamma (B tensor[E] V)` instance is introduced and that the
   rejected left-factor action diamond remains rejected.
4. Decide whether `IsCrystallineRelQp` is mathematically honest vocabulary for an arbitrary supplied
   period ring. If the name remains too suggestive, give one exact neutral replacement. It must never
   be presented as `IsCrystallineAt`, `D_cris`, or a comparison theorem.
5. Check the corrected roles of `xi`, `t`, fixed scalars, and coefficients: `xi` generates
   `ker theta`; `t = log [epsilon]`; `B_cris^Gamma = K0` is a theorem provider; ramified `E` is handled
   only through the deferred `K0 tensor[Qp] E` module architecture.
6. Check that N-Cp and N-PD are genuinely separate missing providers and that N3--N7 are not collapsed
   into a single task. Verify the pin really lacks the claimed continuous `C_p` action, PD envelope,
   `A_cris`, `B_cris`, `D_cris`, and fixed-ring theorem.
7. Identify the smallest exact production slice safe to persist now, if any. Give its declarations,
   imports, dependency order, required docstrings, first residual Lean goal, and exact axiom audits.
8. No `IsCrystallineAt` theorem, comparison theorem, graph mutation, provider promotion, T2 axiom or
   `FLT-MLT-PADIC-HODGE` promotion is authorized by this review.

Return exactly one verdict: `PASS-BOUNDED-SLICE`, `REVISE-MECHANICAL`, `REVISE-SUBSTANTIVE`,
`OBSTRUCTION`, or `NO-RESULT`. A PASS authorizes only the exact methodology probe enumerated in the
report and still requires a controller kernel gate and later independent build review.
