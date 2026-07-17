# GPT-5.6 xhigh independent design review

Component: `cyclic-base-change / FLT-CBASE`  
Agent: `gpt56xhigh-independent-reviewer-d10`  
Model/backend: `gpt-5.6-sol` / Codex `exec`  
Verdict: **REVISE**  
Fable trigger: **YES**

---

# REVISE

The forward/descent orientation is correct, but the artifact is neither buildable as written nor an acceptable exact T2 interface.

1. **D1 fails with the proposed type.** The signature at [stage-1-opus48-primary.md:191](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/cyclic-base-change/stage-1-opus48-primary.md:191) lacks the rational algebra/module and scalar-tower structure. Lean fails to synthesize `Module ℚ F`.

   This corrected version was checked successfully and has exactly `[propext, Classical.choice, Quot.sound]`:

   ```lean
   theorem GaloisRep.even_finrank_of_even_base
       {F E : Type*}
       [Field F] [NumberField F]
       [Field E] [NumberField E] [Algebra F E]
       (hF : Even (Module.finrank ℚ F)) :
       Even (Module.finrank ℚ E) := by
     rw [← Module.finrank_mul_finrank ℚ F E]
     exact hF.mul_right _
   ```

2. **D4/D5 are directionally right but not exact interfaces.** D4 is correctly `F → E`, and D5 correctly reverses it, matching the existing iff at [Automorphic.lean:190](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:190). But “same context” and “same context + …” are not full Lean types. More importantly, D5 merely restates the reverse implication; it is not the promised image characterization with invariant characters, twists, and multiplicity one. Those signatures remain absent, while the graph explicitly requires image characterization for FLT-CBASE and Brauer descent ([proof-graph.ndjson:13](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-graph.ndjson:13), [proof-graph.ndjson:24](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-graph.ndjson:24)).

3. **The proposed scaffolding violates T2 policy.** Putting D4/D5 under `FLT/` with `sorry` deliberately produces `sorryAx`. T2 instead permits finite, exactly typed, source-linked assumptions; production nodes cannot use replacement `sorry` ([README.md:12](/Volumes/second-store/devel/proof-forks/FLT/methodology/README.md:12), [IMPLEMENTATION-PLAN.md:126](/Volumes/second-store/devel/proof-forks/FLT/methodology/IMPLEMENTATION-PLAN.md:126)). Live audit confirms the current theorem still has `sorryAx`. Such scaffolds may live in methodology probes, but cannot constitute T2 closure.

4. **They are not yet source-exact named T2 boundaries.** The register contains only incomplete blueprint source `SRC-004` ([SOURCE-REGISTER.md:12](/Volumes/second-store/devel/proof-forks/FLT/methodology/SOURCE-REGISTER.md:12)); it has no primary Langlands/Arthur–Clozel or Jacquet–Langlands entry. The blueprint itself says image characterization needs multiplicity one and JL ([ch04overview.tex:86](/Volumes/second-store/devel/proof-forks/FLT/blueprint/src/chapter/ch04overview.tex:86)). Consequently, hypothesis minimization—including the claim that `hρirred` belongs only to D5—cannot yet be frozen source-faithfully. Restriction irreducibility may also be needed to keep forward base change cuspidal.

5. **D2 is only partly “thin.”** I verified kernel-clean lemmas for membership in `preimageComapFinset` and transport of `p ∉ v`. That definition, however, provides no conductor, `U₁`, tame-quotient, or local automorphic compatibility. Those remain substantive boundaries.

6. **The predicted first D4 residual goal is premature.** The existing tensor-product instance supplies only `IsQuaternionAlgebra E (E ⊗[F] D)` ([Automorphic.lean:99](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:99)). The target predicate first requires a `DivisionRing` and `WithRigidification` ([Automorphic.lean:84](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:84)); no base-change adapters for those were found. The Hecke-eigensystem transport is therefore not the first residual.

The artifact is correct that the theorem is solvable-Galois rather than merely cyclic, that there are no real Lean consumers yet, and that coefficient transport belongs to the Brauer-family obligation.

**Fable trigger: YES.** The advertised first signature fails Lean elaboration, and implementing the proposed D4/D5 tranche would fail the target-stage axiom audit. Both are conditional-diversity triggers under the current ladder ([flt-completion README:14](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/README.md:14)).

**Next exact probe:** land the corrected D1 signature above in an isolated probe, then probe the already validated D2 endpoint:

```lean
theorem goodPlace_of_mem_preimageComapFinset
    {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (p : 𝓞 F) ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 E))
    (hw : w ∈ HeightOneSpectrum.preimageComapFinset
      (𝓞 F) F E (𝓞 E) S) :
    (p : 𝓞 E) ∉ w.asIdeal
```

This probe also returned exactly the standard axiom trio. No files were edited.

