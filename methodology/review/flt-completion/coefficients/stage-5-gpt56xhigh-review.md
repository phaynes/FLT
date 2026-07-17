REVISE

Classification: **substantive mathematical/statement-level**, with additional mechanical universe and packaging repairs. The synthesis preserves most Stage-2 corrections and the same-`O` Fable comparison argument, but it does not preserve the complete Fable coefficient boundary or the actual consumer ledger.

1. **Signatures are not yet frozen exactly.** Explicit `(O : Type uO)`, `IsDomain O`, DVR, fraction-field, scalar, and residual discrete-topology data are correct. But Fable retained the generic embedding `[Algebra E (AlgebraicClosure ℚ_[p])]` and its continuous scalar action ([Stage 3](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/coefficients/stage-3-fable5-diversity.md:52)); Opus explicitly drops them ([Stage 4](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/coefficients/stage-4-opus48-synthesis.md:77)). They cannot simply disappear: `cyclic_base_change` and `mem_isCompatible` use precisely such integral-to-\(\overline{\mathbb Q}_p\) base changes.

   The production signature must either retain a chosen generic-closure embedding/tower or introduce a separate explicit source-closure wrapper. It must also quantify `V0`, `W₁`, and `W₂` at named universes; `GroupContract.{uO,uF,0,0}` is valid only for the temporary `Type 0` specialization. The generalized boundary is `GroupContract.{uO,uF,uW1,uW2}`.

   One further live mismatch is confirmed: the current assumptions do **not** synthesize  
   `IsLocalHom (algebraMap ℤ_[p] (ResidueField O))`, which `lifts` requires. This needs a named T-A2/glue adapter, not silent inference.

2. **Keep `IsDiscreteValuationRing O`.** Mathlib requires the separate `[IsDomain O]` and makes DVR a local PID, but not automatically a complete coefficient ring ([DVR API](/Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:56)). Taylor’s notes first define residual reduction via an integral lattice and later reduce to \(O_L\), the integers of a finite extension \(L/\mathbb Q_\ell\) ([Taylor notes](https://math.berkeley.edu/~fengt/249A_2018.pdf)). The source/order layer should therefore remain DVR-strength. Export a weaker complete-Noetherian-local adapter for deformation consumers; do not weaken the source interface itself.

3. **Use `extends StableLatticeData`.** A read-only universe-general probe confirmed that this form elaborates and audits to exactly `[propext, Classical.choice, Quot.sound]`, producing the useful `toStableLatticeData` projection. The flat form merely duplicates fields and makes later source/p-adic-Hodge adapters more fragile.

4. **The two-lattice characteristic-polynomial route is valid, but only for the same `O`.** The trio-clean route is:

   - prove pointwise that `GaloisRep.baseChange` acts as `LinearMap.baseChange`;
   - use both generic-fibre compatibility equations and conjugacy invariance of charpoly;
   - apply `LinearMap.charpoly_baseChange`;
   - descend polynomial equality through `IsFractionRing.injective`;
   - map that equality to the residue field and compose with both `IsSemisimplifiedResidualModel` charpoly witnesses.

   I replayed this successfully with arbitrary module universes. It proves raw charpoly agreement across two integral models over one coefficient ring. It does not prove cross-`O` comparison or semisimple equivalence.

5. **Exact proved/open boundary:**

   - Bankable with the standard trio: data structures, existence *predicates*, closure-comparison propositions, `galoisRep_baseChange_apply`, both charpoly lemmas, residual rank transport, and the implication `GroupContract → LatticeIndependent`.
   - Still open: T-A1 stable-lattice existence; T-A2 coefficient/local-hom/completeness glue; T-A3 semisimplification existence; M4 semisimplicity ascent; BN itself; and T-IND-CLOSURE/cross-coefficient comparison.
   - [`specializedResidualModelsUnique`](/Volumes/second-store/devel/proof-forks/FLT/FLTMethodology/Probes/BrauerNesbittBoundary.lean:405) and the general bridge are conditional wiring, not discharged Brauer–Nesbitt theorems.
   - T1 permits only `knownin1980s` plus the standard trio ([policy](/Volumes/second-store/devel/proof-forks/FLT/methodology/README.md:8)); explicit contract arguments do not close the corresponding graph nodes.

6. **Correct live-consumer ledger:**

   | Declaration | Exact relationship | Closure |
   |---|---|---|
   | [`IsAutomorphicOfLevel`](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:70) | Generic coefficient side only | clean |
   | [`cyclic_base_change`](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:137) | Direct integral model and base-change/conjugacy to `AlgebraicClosure ℚ_[p]` | `sorryAx` |
   | [`mem_isCompatible`](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Family.lean:37) | Direct integral/closure coefficient consumer | `sorryAx` |
   | [`lifts`](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/HardlyRamified/Lift.lean:37) | Reverse residual-to-integral boundary; additionally requires `IsLocalHom` | `sorryAx` |
   | [`ProartinianCat.self`](/Volumes/second-store/devel/proof-forks/FLT/FLT/Deformations/Categories.lean:180) | Weaker complete-Noetherian-local view | clean; representability theorem remains `sorryAx` |

   Thus Stage 4’s “actual live consumers” list is incomplete, and its reason for removing the generic closure embedding is false.

7. **`MLTCoefficientData.lean` is not yet a sound production slice.** The file is currently absent, and the synthesis does not contain the exact declarations it calls frozen. It can become a sound methodology probe after the signature and ledger repairs above; it must not promote `FLT-MLT-COEFFICIENTS`.

**Additional Fable pass:** **REQUIRED** under the typed rule. Difficulty is 10 and the revision changes source/consumer statement boundaries, not merely syntax.

**Next exact build/probe unit:** `FLTMethodology/Probes/MLTCoefficientData.lean`, containing generalized-universe `StableLatticeData`, `CoefficientData extends StableLatticeData`, an explicit generic-closure/tower wrapper, the residue local-hom adapter as an open named boundary, closure comparison with named embeddings, `galoisRep_baseChange_apply`, the two charpoly lemmas, and conditional BN wiring. Gate it with:

```text
lake build FLTMethodology.Probes.MLTCoefficientData
```

Every banked declaration must audit to the standard trio, and the file should remain unregistered/unpromoted until the additional Fable review. Review completed read-only at final checkout `8205636`; the reviewed files and APIs did not change during the intervening branch advance.

