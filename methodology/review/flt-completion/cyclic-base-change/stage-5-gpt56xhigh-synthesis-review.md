# REVISE-SUBSTANTIVE

The bounded structural slice is kernel-clean, but the synthesis overstates consumer preservation and contains an under-specified Galois-fiber interface.

1. **Universe obstruction — confirmed, scope claim overstated.**  
   `cyclic_base_change` has independent universes `u₁`, `u₂`; its `E`-side witness must inhabit `Type u₂`, while the literal tensor witness has type `Type (max u₁ u₂)`. The replay failed exactly with:

   ```text
   failed to solve universe constraint
     u₂ =?= max u₁ u₂
   ```

   Thus the obstruction is real for the in-tree tensor witness. A new single-universe methodology interface does not mutate the frozen theorem and breaks no live application because there are no live applications. But the claim that both planned graph consumers are necessarily `Type 0` is unsupported: both declarations are absent, and existing compatible-family vocabulary is universe-polymorphic. “Zero scope loss” cannot be asserted for those future consumers. See [stage-4 synthesis](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/cyclic-base-change/stage-4-opus48-synthesis.md:51) and [Automorphic.lean](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:137).

2. **Automorphy-definition gap — confirmed and correctly owned.**  
   `IsAutomorphicOfLevel` requires `DivisionRing`, `IsQuaternionAlgebra`, and `WithRigidification`, but neither `IsTotallyDefinite` nor even degree. The docstring is stronger than the type. A quaternion algebra unramified at finite places may ramify at only a proper even subset of real places, so the formal witness need not be totally definite. This belongs to `FLT-AUT-DEF`, not a base-change provider. See [the exact existential](/Volumes/second-store/devel/proof-forks/FLT/FLT/GaloisRepresentation/Automorphic.lean:84).

3. **Lean replay.**  
   With only:

   ```lean
   import FLT.GaloisRepresentation.Automorphic
   ```

   these four exact theorem signatures elaborated:

   ```lean
   theorem even_finrank_of_even_base
       {F E : Type*} [Field F] [NumberField F]
       [Field E] [NumberField E] [Algebra F E]
       (hF : Even (Module.finrank ℚ F)) :
       Even (Module.finrank ℚ E)

   theorem mem_preimageComapFinset_iff
       {F E : Type*} [Field F] [NumberField F]
       [Field E] [NumberField E] [Algebra F E]
       (S : Finset (HeightOneSpectrum (𝓞 F)))
       (w : HeightOneSpectrum (𝓞 E)) :
       w ∈ HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S ↔
         w.under (𝓞 F) ∈ S

   theorem natCast_notMem_of_mem_preimageComapFinset
       {F E : Type*} [Field F] [NumberField F]
       [Field E] [NumberField E] [Algebra F E]
       (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
       (hS : ∀ v ∈ S, (p : 𝓞 F) ∉ v.asIdeal)
       (w : HeightOneSpectrum (𝓞 E))
       (hw : w ∈ HeightOneSpectrum.preimageComapFinset
         (𝓞 F) F E (𝓞 E) S) :
       (p : 𝓞 E) ∉ w.asIdeal

   theorem heckeAlgebra_algHom_ext
       {F : Type*} [Field F] [NumberField F]
       {D : Type*} [DivisionRing D] [Algebra F D]
       [IsQuaternionAlgebra.NumberField.WithRigidification F D]
       {R : Type*} [CommRing R]
       {p : ℕ} (𝒮 : U₁Data F R p) (hQ : 𝒮.Q = ∅)
       {A : Type*} [CommRing A] [Algebra R A]
       (π π' : HeckeAlgebra D 𝒮 →ₐ[R] A)
       (h : ∀ v hvS hvQ,
         π (HeckeAlgebra.T D 𝒮 v hvS hvQ) =
           π' (HeckeAlgebra.T D 𝒮 v hvS hvQ)) :
       π = π'
   ```

   Every one audited to exactly:

   ```text
   [propext, Classical.choice, Quot.sound]
   ```

   B3 is eigensystem extensionality, not multiplicity one.

   V1, V2, V5, V8, Q1, Q2, V3, and V4 also elaborate as `Prop` definitions with that trio. This establishes only that their definitions typecheck. V6/V7/V9 are not given with complete binder lists in the synthesis and are absent from its final replay log, so their exact claimed signatures are not bankable from this artifact.

4. **Substantive counterexample to V5.**  
   `BaseChangeFiberUpToTwist` omits the hypotheses needed for Clifford/Schur theory. Let `E/F` be quadratic with character `ε`, and take:

   \[
   \rho=1\oplus\varepsilon,\qquad \sigma=1\oplus1.
   \]

   Their restrictions to \(G_E\) are equal. But for \(g\notin G_E\), no scalar character \(\chi\) can make
   \(\sigma=\chi\otimes\rho\): the right side has eigenvalues \(a,-a\), while the left side is the identity. Conjugating `σ` changes nothing. V5 therefore needs, at minimum, a finite Galois extension, field/algebraically-closed coefficient conditions, finite-dimensionality, and irreducibility of the restricted representation—or it must remain merely a broad property with a separately stated conditional theorem. The current claim that it is a ready algebraic residual is not justified. See [stage-4 V5 claim](/Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/cyclic-base-change/stage-4-opus48-synthesis.md:144).

5. **Analytic and graph boundary.**  
   Forward transfer and reverse descent are correctly oriented. The genuine analytic closure still includes base change, image characterization, cuspidality, Jacquet–Langlands, strong multiplicity one, and level/conductor compatibility. V3/V4 honestly define the final implications but merely package those results; their standard-trio audits do not prove them. The synthesis is also internally inconsistent in saying the forward route is `JL⁻¹ ∘ base change ∘ JL` while later claiming `FLT-JL` feeds descent only. The live `FLT-CBASE` row lists only `FLT-AUT-DEF`, so the proposed provider closure is not yet reflected exactly. No graph change is authorized here.

6. **Source gate — honest.**  
   `SRC-004` is explicitly incomplete. There is no registered primary base-change, Jacquet–Langlands, or multiplicity-one locator. Langlands is named only generically; Arthur–Clozel has no in-tree source row. The synthesis fabricates no theorem/page locator and authorizes no `knownin1980s`, custom T2 axiom, new `sorry`, or promotion. This part is sound.

7. **Safe bounded probe disposition.**  
   The four B declarations above are mechanically safe for a methodology-only probe. They have no residual Lean goal. They are not proof progress and do not affect `cyclic_base_change`.

   The next residuals are:

   - Frozen two-universe theorem: `u₂ =?= max u₁ u₂`.
   - Single-universe tensor route: exactly `DivisionRing (E ⊗[F] D)`.
   - Then `WithRigidification E (E ⊗[F] D)`.
   - Only afterward come level/Frobenius transport and the analytic boundaries.

No files, task state, source rows, graph rows, or public declarations were edited. A concurrent external process changed unrelated worktree/control files during the review; all adjudication above is tied to immutable `c6c1a7d`.
