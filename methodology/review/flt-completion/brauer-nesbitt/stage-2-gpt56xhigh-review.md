# GPT-5.6 xhigh independent design review

Component: `brauer-nesbitt / FLT-BRAUER-NESBITT`  
Agent: `gpt56xhigh-independent-reviewer-d8`  
Model/backend: `gpt-5.6-sol` / Codex `exec`  
Verdict: **REVISE**  
Fable trigger: **YES**

---

# REVISE

The arbitrary-field umbrella should remain, and L1 is sound. The artifact is not build-ready because L3 is neither an exact elaborating signature nor an imperfect-field-complete design.

- **Umbrella: retain.** The frozen [`Contract`](/Volumes/second-store/devel/proof-forks/FLT/FLT/Components/Contracts/BrauerNesbitt.lean:34) correctly assumes finite-dimensional semisimple representations over an arbitrary field and full characteristic-polynomial equality on every group element. It does not silently require algebraic closure, perfectness, characteristic zero, or finite `G`.

- **L1: verified.** At current HEAD `fa6ab03`, pinned Mathlib `a3364fa`, and Lean `4.32.0-rc1`, I kernel-checked read-only stdin proofs of:
  `jointImageAlgHom_surjective`,
  both module-semisimplicity transports, and
  `isSemisimpleRing_jointImageAlgebra`.
  Every proof had axiom closure `[propext, Classical.choice, Quot.sound]`. Thus the mathematics at [L1–L2](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/brauer-nesbitt/stage-1-opus48-primary.md:165) is sound. One API citation is wrong: pinned Mathlib has no declaration named `Submodule.finite`; finite-dimensionality is nevertheless inferred through the submodule instance.

- **L3: revise before freezing.**
  1. The literal `hspan` expression at [L202](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/brauer-nesbitt/stage-1-opus48-primary.md:197) fails elaboration with `expected type must be known`. It needs an explicit coercion such as:
     ```lean
     Submodule.span k ((fun u : Aˣ => (u : A)) '' U) = ⊤
     ```
  2. The type records only `U : Set Aˣ`, while the proposed proof explicitly invokes “group closure.” Either encode multiplicative closure, specialize to an actual homomorphism `G →* Aˣ`, or provide a source-complete proof that an arbitrary spanning set of units suffices.
  3. Artin–Wedderburn over division rings does not itself solve the imperfect-field step. For a purely inseparable degree-`p` field extension `K/k`, the finite-dimensional semisimple algebra `A = K` has a simple module whose `k`-valued trace character is identically zero. Therefore any unspoken reduction to independence/nonvanishing of simple trace characters is invalid. Full characteristic polynomials may still recover multiplicities, but the required `p`-power/inseparability argument is exactly the missing theorem. L3 is **uncertain, not refuted**.

- **Consumers are overstated.** The two existing Lean declarations are alternative conditional bridges to the same same-field residual target, not two discharged production consumers. The residual relation explicitly supplies semisimplicity, but the compatible-family interface supplies only almost-all Frobenius data; Chebotarev continuity, semisimplicity, coefficient comparison, and descent remain open. See [`isCompatible`](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean:58) and the admitted family construction at [`mem_isCompatible`](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Family.lean:37).

- **Source/stage closure remains open.** The source packet itself says `PARTIAL - NOT READY FOR TERMINAL IMPLEMENTATION` and requires an imperfect-field-safe multiplicity signature before freezing ([packet](/Volumes/second-store/devel/proof-forks/FLT/methodology/source-design/brauer-nesbitt.md:120)). `SRC-018` is not the arbitrary-field theorem; `SRC-019` is secondary; Curtis–Reiner is still unregistered/unverified. Moreover, the live obligation still cites only `SRC-003` ([obligation](/Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-obligations.ndjson:30)). L1 meets the T3 axiom policy, but L3 and the terminal meet neither the kernel nor source gate.

- **Telemetry:** the latest recorded build is green but remains at `G4 = false`, with `11/52` nodes proved and 49 critical-path nodes open; `FLT-BRAUER-NESBITT` remains absent ([progress](/Volumes/second-store/devel/proof-forks/FLT/methodology/output/flt-progress.ndjson:86)). No files were edited during this review.

**Fable trigger: YES.** The literal L3 signature failed elaboration, and the arbitrary-set/imperfect-field proof architecture remains materially uncertain. Both qualify under the conditional-diversity rule in the [completion ladder](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/README.md:14).

**First exact kernel build unit:** `FLTMethodology/Probes/BrauerNesbittAlgebra.lean`, in this order:

1. `jointImageAlgHom : k[G] →ₐ[k] jointImageAlgebra rho sigma`
2. `jointImageAlgHom_surjective`
3. reducible `fstModule` / `sndModule`
4. `isSemisimpleModule_fst` / `_snd`
5. `isSemisimpleRing_jointImageAlgebra`

That entire tranche is already kernel-green in the read-only probe. Bank it before attempting a corrected and source-adjudicated L3.

