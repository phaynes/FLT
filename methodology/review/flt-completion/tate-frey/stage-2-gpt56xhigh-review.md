# Stage 2 independent review — GPT-5.6 xhigh

## Model and transport evidence

- Agent: `gpt56xhigh-independent-reviewer-d8`
- Configured model: `gpt-5.6-sol`
- Backend transport: `codex`
- Role: `primary`
- Review budget: `1800 s`
- Exit code: `0`
- Actual invocation elapsed: `467232 ms`
- Codex session: `019f6f0c-0fbb-7020-aa76-0a3db9e575d4`
- Input tokens: `4,393,053`
- Cached input tokens: `4,171,008`
- Output tokens: `22,099`
- Reasoning output tokens: `15,387` (reported subset of output tokens)
- Total tokens: `4,415,152`
- Output characters: `4776`
- Bridge topology: `single`
- Bridge total duration: `467233 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/tate-frey/stage-2-prompt-gpt56xhigh-review.md`
- Repository mutation authority: read-only; no model edits permitted

## Full review output

REVISE

The two regressions remain valid: fresh audits of `FreyCurve.torsion_rank` and `WeierstrassCurve.galoisRep` returned exactly `[propext, Classical.choice, Quot.sound]`. The primary design nevertheless cannot advance to build.

- The unramified decomposition is materially false. The report claims every prime away from `2·P.p` gives good reduction. If an odd `q ≠ P.p` divides `abc`, the Frey curve instead has multiplicative reduction; the required route uses Tate uniformization, `FreyCurve.j_valuation_of_bad_prime`, the `P.p ∣ v_q(j)` Kummer argument, and local/global torsion transport. The repository blueprint explicitly separates these cases ([ch03freyold.tex](/Volumes/second-store/devel/proof-forks/FLT/blueprint/src/chapter/ch03freyold.tex:208)). Tate theory is therefore required beyond the prime-two quotient.

- The proposed `WeilPairingData` signature does not elaborate. A direct read-only Lean probe failed on all three `σ • …` expressions. Moreover, `σ : k ≃ₐ[k] k` is the wrong Galois group and makes equivariance vacuous; the correct action is `Gal(AlgebraicClosure K/K)` through `torsionGaloisMap`. Its `perfect` field states only left nondegeneracy, not perfectness as an isomorphism with the dual. The current zero-pairing counterexample is real ([WeilPairing.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean:38)), but zero pairing does not imply determinant zero—it supplies no determinant constraint.

- Determinant normalization is incomplete. The design needs an exact theorem deriving the determinant identity from a perfect equivariant pairing, followed by `cyclotomicCharacter.toZModPow` at exponent `1` to match the `ZMod P.p` consumer. Merely listing both cyclotomic-character APIs does not build the field in [Defs.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Defs.lean:107).

- The residue-characteristic flatness analysis identifies the foundational API gap but omits necessary interfaces: the multiplicative branch needs the Frey-specific valuation/Kummer condition and quadratic-twist descent; the good branch still needs an adapter from the local Hopf-algebra theorem to the global `IsFlatAt` representation and all open ideals of `ZMod P.p`. Those are not mechanical consequences of [Flat.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/KnownIn1980s/EllipticCurves/Flat.lean:145).

- The dependency graph is inconsistent: the report makes WEIL an independent slice while also requiring `tateEquivSepClosure` for its normalization. Either add `FLT-TATE-UNRAMIFIED → FLT-TATE-WEIL`, or move normalization to an explicit join node. Consequently the final [torsion_isHardlyRamified](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Frey.lean:52) assembly is not yet a bounded mechanical build.

- The proposed universal resultant theorem is not justified as the smallest first tranche. Coprimality alone does not supply point specialization or torsion injectivity; [Flat.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/KnownIn1980s/EllipticCurves/Flat.lean:192) also requires a companion separability/discriminant input.

- The T1 policy choice is misstated. T1 permits the visible `knownin1980s` boundary plus the standard axioms—not new custom declared axioms ([methodology README](/Volumes/second-store/devel/proof-forks/FLT/methodology/README.md:8)). A named theorem auditing to `knownin1980s` is possible; a new custom “source-gate axiom” is not. SRC-024 also remains visually unchecked, and the live component row remains `PARTIAL` with `primary_source_exact=false`.

Fable-diversity trigger: **yes**. The proposed primary interface failed exact Lean elaboration, which qualifies as a failed signature build under the conditional-diversity rule; the omitted multiplicative-prime branch is also architectural rather than stylistic.

Next exact buildable probe: `WeilPairingDataBoundary`, using this signature, which I verified read-only to elaborate with only the standard axiom trio:

```lean
structure WeierstrassCurve.WeilPairingData
    (K : Type u) [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)]
    (n : ℕ) [NeZero n] [NeZero (n : AlgebraicClosure K)] where
  pair : E.AbsoluteTorsion n →+ E.AbsoluteTorsion n →+
    Additive (rootsOfUnity n (AlgebraicClosure K))
  alternating : ∀ P, pair P P = 0
  perfect : Function.Bijective pair
  galois_equivariant : ∀ (σ : Field.absoluteGaloisGroup K) P Q,
    pair (E.torsionGaloisMap n σ P) (E.torsionGaloisMap n σ Q) =
      Additive.ofMul
        (σ.toRingEquiv.toMulEquiv.restrictRootsOfUnity n (pair P Q).toMul)
```

No repository files were edited.
