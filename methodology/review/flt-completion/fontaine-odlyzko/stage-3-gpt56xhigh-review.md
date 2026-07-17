# Stage 3 independent comparison — GPT-5.6 xhigh

## Model and transport evidence

- Agent: `gpt56xhigh-independent-reviewer-d10`
- Configured model: `gpt-5.6-sol`
- Backend transport: `codex`
- Role: `primary`
- Review budget: `2100 s`
- Exit code: `0`
- Actual invocation elapsed: `506108 ms`
- Token count: `5,184,301` input; `4,965,376` cached input; `22,170` output; `13,695` reasoning output (included in output); `5,206,471` total
- Output characters: `6069`
- Bridge topology: `single`
- Bridge total duration: `506109 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/fontaine-odlyzko/stage-3-prompt-gpt56xhigh-review.md`
- Repository mutation authority: read-only; no model edits permitted

## Full review output

REVISE

Fable gives a plausible paper-level repair, but not a source-gated or Lean-freezable decomposition. The route is not disproved; it requires exact interfaces and additional verification.

1. Mathematical completeness

Conditional on three unresolved results—Fontaine’s different bound, local flat splitting in the reversed reducible orientation, and inertia cyclicity at 2—the full-linear-image split plausibly avoids both discriminant tables and Dickson:

- For \(n<18\) with \(3\nmid n\), tame discriminant bounds plus Minkowski can eliminate the surviving degrees.
- For \(3\mid n<18\), the Sylow argument reduces the non-normal case to \(n=12\), \(G\simeq A_4\), then excludes a faithful two-dimensional representation in characteristic \(3\).
- Larger projective exceptional images have sufficiently large full linear image and enter the Odlyzko branch.

This is not yet a complete proof graph: those three conditional steps, local-to-global discriminant assembly, and the general-\(k\) Kummer bridge remain untyped. Opus was also wrong that Dickson was absent: the live repository contains [Dickson classification](/Volumes/second-store/devel/proof-forks/FLT/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean:54), and a read-only `#print axioms` check returned only `propext`, `Classical.choice`, and `Quot.sound`.

2. Quotient orientation

Yes, the exact consumer requires a trivial quotient: a surjective functional invariant under all \(G_\mathbb Q\), hence
\[
0\to\chi_3\to V\to\mathbf1\to0.
\]
That follows directly from [ModThree.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27). Fable’s Kummer example makes the opposite universal “trivial sub” orientation untenable, but it does not itself prove the consumer theorem.

There is presently no kernel consumer: `three_adic` has the import commented out and remains admitted. The downstream edge is currently a control-graph intention, not a compiled dependency.

3. The \(e_2=9\) branch

The hole is real as a missing proof, not an additional mathematical premise.

`IsHardlyRamified.isTameAtTwo` only provides an unramified rank-one quotient and its square-one character; it does not state that the full inertia image is cyclic. From determinant and quotient data one gets an elementary abelian 3-group. Ruling out \(C_3^2\) requires proving that wild inertia maps trivially and the resulting tame-inertia quotient is cyclic. No exact pinned lemma or elaborating S11 signature was supplied. Until that bridge exists, the discriminant calculation must allow \(e_2=9\).

4. Historical assumptions

| Input | Exact type | Exact source | Scope verdict |
|---|---|---|---|
| `Odlyzko_statement` | Yes | Registered as SRC-007 | Existing but still subject to the T2 human agreement/audit gate |
| N1 `Fontaine_statement` | No: ellipses, undefined `differentExponent` and local field | Fontaine citation is plausible but absent from the source register and its normalization/corollary is unpinned | Narrower in intent than the core, but strict narrowing cannot be audited without a type |
| N2 `FlatLocalSplit_statement` | No: undefined action predicates, section law, and equivariance | Explicitly marked locator-pending by Fable | Not source-ready; general \(k=\mathbb F_{3^r}\) introduces hidden finite-flat and \(k\)-equivariance transport |

An external spot-check supports plausibility, not authorization: a modern exposition derives the \(3^{3/2}\) Fontaine root-discriminant bound, while Mazur’s primary paper treats trivial extensions in an admissible-group-scheme setting rather than Fable’s exact arbitrary-\(k\) proposition. [Fontaine-bound exposition](https://web.stanford.edu/~dkim04/sags-2510/2025-10-22/), [Mazur 1977](https://www.numdam.org/article/PMIHES_1977__47__33_0.pdf).

The current [historical-assumption registry](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/historical-assumptions.ndjson:1) permits no T2 assumption before exact independent review. A human gate remains mandatory for every axiom dependency.

5. Produced infrastructure

| Component | Result |
|---|---|
| D: cut-out field/discriminant | Not elaborating. Hidden obligations include open-kernel finiteness, Galois/cardinality identification, complex-conjugation transport, local different normalization, and primewise assembly. |
| E: Kummer bridge | Not elaborating. It hides continuous \(H^1\), extension-class extraction with the correct orientation, the general-\(k\) tensor comparison, local-condition transport, and \(k\)-linear independence. |
| F: inertia bridge | No signature at all—only a comment. It hides decomposition-group embeddings and the identification between FLT’s inertia subgroup and ramification-index/different APIs. |

Fable itself concedes these signatures are merely drafted at [lines 382–385](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/fontaine-odlyzko/stage-1-fable5-alternative.md:382).

6. First unit and residual

The smallest kernel-buildable unit is only:

```lean
theorem charP_three_of_zp3_algebra
    (k : Type u) [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3
```

I verified this read-only through Lean stdin at the pinned toolchain; its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.

The first likely residual goal is the exact arbitrary-\(k\) reducibility bridge: extract a stable rank-one submodule and quotient character from `¬ ρ.IsIrreducible`, with ranks, actions, and quotient orientation all explicitly typed. Fable’s S3 uses undefined placeholders such as `stable`, `charOfSub`, and `~perm~`.

Opus and Fable do not have enough agreement to freeze a repaired governed component graph. They support freezing only the exact consumer orientation, the characteristic-three lemma, and a provisional list of unresolved nodes. N1, N2, D, E, F, and S11 must each receive exact signatures and source audits first. No repository files were edited, no axiom registered, and no obligation promoted.
