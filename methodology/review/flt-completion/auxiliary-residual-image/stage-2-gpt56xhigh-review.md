# REVISE

Classification: `SUBSTANTIVE-MATHEMATICAL-OR-STATEMENT-LEVEL`  
Typed diversity rule: **Fable pass triggered** because difficulty is 10.  
Promotion: **not authorized**.

Reviewed read-only at final live HEAD `fee713968dafb64725ff653136fad7443a40603e`. The repository advanced during review only through controller status commits; no relevant mathematical or Lean content changed. I made no repository changes.

## Adjudication

The conceptual order

```text
auxiliary-field conditions → auxiliary-curve data → residual-image theorems
```

is acyclic and worth retaining. The submitted realization is not complete or source-exact:

1. **The proposed predicate proves the wrong irreducibility.** Taylor requires absolute irreducibility after restriction to `F(ζℓ)`. Opus uses only `GaloisRep.IsIrreducible` over the original coefficient field. The pin already has `Representation.IsAbsolutelyIrreducible`; it must be used.

2. **The local-field signature is wrong.** Taylor requires the rational application prime to be globally unramified in `F`, not “unramified at one chosen `HeightOneSpectrum` place.” For the two applications, both `ℓ` and `p` require
   `Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)})`. This exact boundary was already independently accepted by the p-adic-Hodge review.

3. **The Opus disjointness fields are ill-oriented.**  
   `Kres Kcyc : IntermediateField F Ω` followed by
   `(⊥ : IntermediateField F Ω).LinearDisjoint Kres`
   expresses the base field against its own extensions, not auxiliary `F/ℚ` against residual and cyclotomic avoidance fields. It is effectively the wrong relation. All fields must be embedded over `ℚ` in one ambient field.

4. **Pairwise disjointness is too weak as primitive data.** The structure should carry disjointness from `Kres ⊔ Kcyc`; the two projections follow from the already kernel-clean `linearDisjoint_of_compositum`.

5. **Moret–Bailly ownership is overstated.** The current independent source review found that MB89 Theorem 1.3 does not directly give Galoisness or arbitrary avoidance-field disjointness. Those require a separate proved provider or an explicitly selected later source such as the candidate BLGGT proposition. [Moret–Bailly review](</Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/moret-bailly/stage-3-gpt56xhigh-review.md:21>)

6. **Good reduction is curve-relative.** The exact API is `WeierstrassCurve.HasGoodReduction R W`, relative to a DVR and its fraction field—not a field-only or bare-place predicate. It belongs to `AuxiliaryCurveData`, after mapping the curve to the completion. The obligation row itself therefore needs statement repair. [Good-reduction API](</Volumes/second-store/devel/proof-forks/FLT/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean:267>)

7. **The two Taylor applications are genuinely different.** The first concerns the coefficient-extended `A[p]` induced representation and needs a Mackey/character-ratio theorem. The second concerns `A[ℓ] ≃ ρ̄|G_F` and needs avoidance/disjointness-to-image-preservation. A conjunctive wrapper may assemble them, but they need separate proof nodes.

8. **Class-field theory is not part of the residual-image proof.** It may construct/globalize the finite-order character and provide prescribed local data. Once `InducedCharacterData` is supplied, cyclotomic irreducibility is representation and field-disjointness mathematics. Full reciprocity should therefore feed a later T2 induced-character provider, not directly gate the T1 residual theorem. This matches the repaired class-field decomposition. [Class-field synthesis](</Volumes/second-store/devel/proof-forks/FLT/methodology/review/flt-completion/class-field/stage-6-opus48-synthesis.md:123>)

9. **Adequacy remains separate.** No adequacy or big-image API exists in this pin. The direct graph edge `FLT-RESIDUAL-IMAGE → FLT-TW-PRIMES` currently lets cyclotomic irreducibility masquerade as Taylor–Wiles adequacy. [Current edge](</Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-graph.ndjson:68>)

10. **The hardly-ramified edge is misdirected.** `FLT-HR-DEF` belongs upstream of auxiliary-curve construction, which receives the original representation. Residual-image proofs consume the concrete curve representations, not the hardly-ramified definition. The current edge points to `FLT-RESIDUAL-IMAGE`. [Current edge](</Volumes/second-store/devel/proof-forks/FLT/methodology/control/proof-graph.ndjson:120>)

## Three irreducibility levels

| Property | Exact status |
|---|---|
| Ordinary residual irreducibility | `GaloisRep.IsIrreducible ρ` |
| Source-required property | Absolute irreducibility of `ρ|G_{F(ζℓ)}` |
| Taylor–Wiles adequacy | Separate stronger/cohomological interface; absent in the pin |

No implication among these may be silently inserted.

Taylor 2018 explicitly requires `ℓ` unramified in `F`, together with absolute cyclotomic-restriction irreducibility. Taylor 2006 is the complete-splitting near-match. [Taylor source contract](</Volumes/second-store/devel/proof-forks/FLT/methodology/MLT-SOURCE-CONTRACT.md:13>) [Blueprint comparison](</Volumes/second-store/devel/proof-forks/FLT/blueprint/src/chapter/ch04overview.tex:79>)

## Accepted kernel-clean signatures

These were elaborated through Lean stdin against the current pin and audited to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

### Cyclotomic absolute irreducibility

```lean
universe uF uk uV

def IsCyclotomicRestrictionAbsolutelyIrreducible
    {F : Type uF} [Field F] [NumberField F]
    {k : Type uk} [Field k] [TopologicalSpace k]
    {V : Type uV} [AddCommGroup V] [Module k V]
    (ell : ℕ) (rho : GaloisRep F k V) : Prop :=
  Representation.IsAbsolutelyIrreducible.{max uF uk uV, uF, uk, uV}
    (rho.map (algebraMap F (CyclotomicField ell F))).toRepresentation

def CyclotomicRestrictionPreservesImage
    {F : Type uF} [Field F] [NumberField F]
    {k : Type uk} [Field k] [TopologicalSpace k]
    {V : Type uV} [AddCommGroup V] [Module k V]
    (ell : ℕ) (rho : GaloisRep F k V) : Prop :=
  Set.range rho =
    Set.range (rho.map (algebraMap F (CyclotomicField ell F)))
```

This replaces the unused abstract `L`, fabricated `hL : True`, and ordinary irreducibility in the Opus predicate.

### Field-only conditions

```lean
structure AuxiliaryFieldCondition
    (F Omega : Type*) [Field F] [NumberField F]
    [Field Omega] [Algebra ℚ Omega]
    (iotaF : F →ₐ[ℚ] Omega)
    (Kres Kcyc : IntermediateField ℚ Omega)
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime] : Prop where
  ellUnramified :
    Algebra.IsUnramifiedIn (𝓞 F)
      (Ideal.span ({(ell : ℤ)} : Set ℤ))
  pUnramified :
    Algebra.IsUnramifiedIn (𝓞 F)
      (Ideal.span ({(p : ℤ)} : Set ℤ))
  disjointAvoidance :
    iotaF.fieldRange.toSubalgebra.LinearDisjoint
      (Kres ⊔ Kcyc).toSubalgebra
  totallyReal : NumberField.IsTotallyReal F
  evenDegree : Even (Module.finrank ℚ F)
  galoisOverRat : IsGalois ℚ F
```

Good reduction is intentionally absent.

### Curve-relative and induced data

```lean
def HasGoodReductionAt
    {F : Type*} [Field F] [NumberField F]
    (A : WeierstrassCurve F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Prop :=
  (A.map (algebraMap F (v.adicCompletion F))).HasGoodReduction
    (v.adicCompletionIntegers F)

structure InducedCharacterData
    {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    {k : Type*} [Field k] [TopologicalSpace k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (rho : GaloisRep F k V) where
  degreeTwo : Module.finrank F E = 2
  character : GaloisRep E k k
  finiteCharacterImage :
    (Set.range (fun sigma => character sigma)).Finite
  equivInduced :
    rho.toRepresentation.Equiv
      (Representation.ind
        (Field.absoluteGaloisGroup.map
          (algebraMap F E)).toMonoidHom
        character.toRepresentation)
```

The auxiliary-curve data boundary should use:

- `Representation.Equiv`, not `≃ₜ*`, for `A[ℓ] ≃ ρ̄|G_F`;
- coefficient-extended `A[p]` before applying `InducedCharacterData`;
- `HasGoodReductionAt A v` above both primes;
- explicit `GaloisRep.IsFlatAt` fields if the blueprint-flat boundary is retained;
- no irreducibility or adequacy field.

The full `exists_auxiliary_curve` theorem is not signature-ready. In particular, the current `IsHardlyRamified` interface requires `[Algebra ℤ_[ℓ] R]`, while that instance does not synthesize for `R = ZMod ℓ` in this pin. This is a named HR/coefficient bridge, not permission to insert `True`.

## Gate ownership

- `G-MB-TOPOLOGY`: `FLT-MORET-BAILLY`; local-point topology and source-exact point theorem.
- `G-AUX-AVOIDANCE`: new provider; Galoisness and joint avoidance-field disjointness. MB89 does not currently own this conclusion.
- `G-CF-CHAR`: T2 class-field character globalization and prescribed local components.
- `G-IND-IRRED`: pure induced-representation/Mackey character-ratio theorem; independent of reciprocity.
- `G-COEFF`: coefficient extension and transport from curve torsion to Taylor’s selected residual model.
- `G-PH/RACAR`: good-reduction/flatness to crystallinity and RACAR witness-unramifiedness. Good reduction alone is not Taylor hypothesis 7.
- `G-TW-ADEQUACY`: separate adequacy/large-image provider for Taylor–Wiles primes.

## Transitively reduced graph mutation

Do not apply during this review.

```text
Move:
  FLT-HR-DEF → FLT-RESIDUAL-IMAGE
to:
  FLT-HR-DEF → FLT-AUX-CURVE

Refine:
  FLT-CLASS-FIELD → FLT-AUX-CURVE
as:
  FLT-CLASS-FIELD → FLT-INDUCED-CHAR-DATA → FLT-AUX-CURVE

Add:
  FLT-AUX-AVOIDANCE → FLT-AUX-LOCAL-FIELD
  FLT-MLT-PADIC-HODGE → FLT-AUX-LOCAL-FIELD

Split:
  FLT-AUX-CURVE → FLT-RESIDUAL-INDUCED
  FLT-INDUCED-IRREDUCIBILITY → FLT-RESIDUAL-INDUCED

  FLT-AUX-CURVE → FLT-RESIDUAL-AUXILIARY

  FLT-RESIDUAL-INDUCED → FLT-RESIDUAL-IMAGE
  FLT-RESIDUAL-AUXILIARY → FLT-RESIDUAL-IMAGE

Replace:
  FLT-RESIDUAL-IMAGE → FLT-TW-PRIMES
with:
  FLT-RESIDUAL-IMAGE → FLT-TW-ADEQUACY → FLT-TW-PRIMES
```

Remove the direct `FLT-MLT-SOURCE → FLT-RESIDUAL-IMAGE` theorem edge. The source contract consumes the named predicate vocabulary; the concrete residual proofs meet the coefficient/source contract later in `FLT-POTMOD`.

## First landable unit and next theorem

Smallest kernel-clean unit:

```text
FLT.ModularityLifting.IsCyclotomicRestrictionAbsolutelyIrreducible
FLT.ModularityLifting.CyclotomicRestrictionPreservesImage
```

Proposed probe: `FLTMethodology.Probes.CyclotomicRestrictionAbsoluteBoundary`, with `#check` and `#print axioms` only.

First genuine theorem:

```lean
theorem cyclotomicRestrictionAbsolutelyIrreducible_of_preservesImage
    (rho : GaloisRep F k V) (ell : ℕ)
    (habs :
      Representation.IsAbsolutelyIrreducible
        rho.toRepresentation)
    (himage :
      CyclotomicRestrictionPreservesImage ell rho) :
    IsCyclotomicRestrictionAbsolutelyIrreducible ell rho
```

First expected Lean residual: the pin has no lemma transporting `Representation.IsAbsolutelyIrreducible` across equality of action ranges after arbitrary scalar extension. The first implementation obligation is an order isomorphism between the corresponding `Subrepresentation` lattices. After that adapter, the first source-specific mathematical residual is proving `CyclotomicRestrictionPreservesImage` from the joint residual-kernel/cyclotomic avoidance construction.

No source, graph, task, Lean, or review artifact was promoted or edited by this adjudication.

