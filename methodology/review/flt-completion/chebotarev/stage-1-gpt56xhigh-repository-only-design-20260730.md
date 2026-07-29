# GPT-5.6 xhigh repository-only Chebotarev design review

- Model: gpt-5.6-sol
- Effort: xhigh (profile gpt56xhigh-independent-reviewer-d10)
- Invocation: fresh session, read-only
- Duration: 710796 ms
- Transport: success
- Content verdict: REVISE
- Prompt: stage-1-repository-only-design-prompt-20260730.md

# REVISE

No Opus response is persisted in the Chebotarev review directory—only the two prompts. Independently reviewing the repository nevertheless identifies a substantive defect in the current graph proposal: `FLT.CompatibleFamily.equal_of_charFrob_eq` is too broad, its name suggests equality rather than representation equivalence, and the graph folds the density theorem together with representation theory. The route is sound after splitting and narrowing.

Pinned Mathlib is `a3364fa…`; it contains no `NumberField.chebotarev` or equivalent global Frobenius-density result. The exact local Frobenius and topology infrastructure is present. [lake-manifest.json](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/lake-manifest.json:8)

## 1. Strongest theorem provable now without Chebotarev

The strongest deterministic core is not family-specific. For two continuous rank-two Galois representations over the same Hausdorff topological field, characteristic-polynomial equality on any dense subset extends to every Galois element:

```lean
theorem charpoly_eq_of_eqOn_dense
    {K A V W : Type*}
    [Field K]
    [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [AddCommGroup V] [Module A V] [Module.Finite A V]
    [AddCommGroup W] [Module A W] [Module.Finite A W]
    (rho : GaloisRep K A V) (sigma : GaloisRep K A W)
    (hV : Module.finrank A V = 2)
    (hW : Module.finrank A W = 2)
    {D : Set (Field.absoluteGaloisGroup K)}
    (hD : Dense D)
    (hchar : ∀ g ∈ D, (rho g).charpoly = (sigma g).charpoly) :
    ∀ g, (rho g).charpoly = (sigma g).charpoly
```

I elaborated this read-only through Lean’s stdin and audited it to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The proof extends trace and determinant separately:

- Trace is continuous because `LinearMap.trace A V` is linear from the module topology used internally by `GaloisRep`.
- Determinant continuity is already bundled as `GaloisRep.det`.
- Rank-two characteristic polynomials are reconstructed using the proved `LinearMap.charpoly_of_finrank_eq_two`.

Thus no topology on `Polynomial A`, completeness, algebraic closure, or Chebotarev is needed. The exact `GaloisRep` module topology and determinant are in [GaloisRep.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/Deformations/RepresentationTheory/GaloisRep.lean:47).

The strongest conditional end-to-end corollary adds density of Frobenius conjugates, semisimplicity, and then applies the existing theorem:

```lean
theorem nonempty_representationEquiv_of_charFrob_eq_of_dense
    ...
    (hrho : Representation.IsSemisimpleRepresentation rho.toRepresentation)
    (hsigma : Representation.IsSemisimpleRepresentation sigma.toRepresentation)
    ...
    (hdense : Dense (globalArithFrobConjugatesOutside S))
    (hFrob : ∀ v, v ∉ S → rho.charFrob v = sigma.charFrob v) :
    Nonempty
      (Representation.Equiv rho.toRepresentation sigma.toRepresentation)
```

The Brauer–Nesbitt provider itself is exact and standard-trio clean. [RankTwo.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/Components/BrauerNesbitt/RankTwo.lean:33)

## 2. Exact missing density contract

Use the repository’s actual local-to-global map and arithmetic Frobenius:

```lean
open NumberField IsDedekindDomain

local notation "Γ" K => Field.absoluteGaloisGroup K
local notation "Ω" K => HeightOneSpectrum (𝓞 K)

noncomputable def globalArithFrob
    {K : Type*} [Field K] [NumberField K]
    (v : Ω K) : Γ K :=
  Field.absoluteGaloisGroup.map
      (algebraMap K (v.adicCompletion K))
      (Field.AbsoluteGaloisGroup.adicArithFrob v)

def globalArithFrobConjugatesOutside
    {K : Type*} [Field K] [NumberField K]
    (S : Finset (Ω K)) : Set (Γ K) :=
  {g | ∃ v, v ∉ S ∧
      ∃ τ : Γ K, g = τ * globalArithFrob v * τ⁻¹}

def RatArithmeticFrobeniusConjugacyDensity : Prop :=
  ∀ S : Finset (Ω ℚ),
    Dense (globalArithFrobConjugatesOutside (K := ℚ) S)
```

`RatArithmeticFrobeniusConjugacyDensity` is the smallest honest missing contract. It:

- is specialized to the encoded base field `ℚ`;
- quantifies over every finite exceptional set;
- uses arithmetic, not geometric, Frobenius;
- uses the exact map underlying `GaloisRep.toLocal`;
- states density only;
- contains no Galois representation, coefficient field, semisimplicity, characteristic polynomial, or equivalence conclusion.

`GaloisRep.toLocal` is definitionally composition with this absolute-Galois map, so

```lean
(rho (globalArithFrob v)).charpoly = rho.charFrob v
```

is proved by `rfl`. See [GaloisRep.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/Deformations/RepresentationTheory/GaloisRep.lean:305) and [AbsoluteGaloisGroup.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:777).

## 3. Dependency-ordered declaration graph

| Order | Declaration | Dependency/status |
|---|---|---|
| D0 | `globalArithFrob` | Existing `absoluteGaloisGroup.map` and `adicArithFrob`; standard trio |
| D1 | `globalArithFrobConjugatesOutside` | D0; definition |
| D2 | `RatArithmeticFrobeniusConjugacyDensity` | D1; exact missing number-theoretic contract |
| A0 | `charpoly_globalArithFrob` | D0; `rfl`; standard trio |
| A1 | `charpoly_conj` | `LinearEquiv.charpoly_conj`; standard trio |
| A2 | `continuous_trace` | Module topology plus `LinearMap.trace`; standard trio |
| A3 | `charpoly_eq_of_eqOn_dense` | A2, continuous determinant, rank-two formula; standard trio |
| A4 | `charpoly_eq_of_charFrob_eq_of_dense` | D1, A0, A1, A3; standard trio |
| A5 | `nonempty_representationEquiv_of_charFrob_eq_of_dense` | A4 plus proved rank-two Brauer–Nesbitt; standard trio |
| F0 | `isCompatible_charFrob_eq` | Thin restatement of `isCompatible` using `charFrob`; standard trio |
| F1 | Consumer-specific fixed-`p`, fixed-`φ` comparison | F0 plus combined exceptional set, second representation/model, coefficient equality and semisimplicity; still open |

A suitable F0 signature, also elaborated with the standard trio, is:

```lean
theorem isCompatible_charFrob_eq
    {K E : Type*} [Field K] [NumberField K]
    [Field E] [NumberField E] {d : ℕ}
    {rho : GaloisRepFamily K E d}
    (hcompat : rho.isCompatible) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (Pv : HeightOneSpectrum (𝓞 K) → E[X]),
      ∀ {p : ℕ} (hfp : Fact p.Prime)
        (φ : E →+* AlgebraicClosure ℚ_[p])
        (v : HeightOneSpectrum (𝓞 K)),
        v ∉ S → (p : 𝓞 K) ∉ v.asIdeal →
        (rho hfp φ).IsUnramifiedAt v ∧
        (rho hfp φ).charFrob v = (Pv v).map φ
```

The current family definition supplies exactly this and nothing about a second representation or semisimplicity. [GaloisRepFamily.lean](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean:58)

## 4. Required pitfalls and counterexamples

- **Conjugacy:** Chosen Frobenius representatives alone are not guaranteed dense in a nonabelian Galois group. In a finite `S₃` quotient, choices could always select one representative of the transposition class and miss the other singleton open fibres. The union of their conjugacy classes is the sound dense set.

- **Finite exceptions:** Density for all primes does not formally imply density after deleting a finite set. The contract must quantify over `∀ S : Finset …`.

- **Coefficients:** Different `p`, or different embeddings `φ₁ φ₂ : E →+* AlgebraicClosure ℚ_[p]`, give no automatic equality between `(Pv v).map φ₁` and `(Pv v).map φ₂`. Cross-prime members live over different fields and cannot be inputs to `Representation.Equiv` without explicit scalar transport.

- **Family breadth:** `isCompatible` describes one family member against an existential polynomial system. It does not produce the second same-field representation needed by Brauer–Nesbitt.

- **Semisimplicity:** It is not part of `GaloisRepFamily.isCompatible`. Without it, the conclusion is false: a nontrivial unipotent representation of `ℤ` and the two-dimensional trivial representation have the same characteristic polynomial on every element but are not equivalent.

- **Trace is insufficient:** `three_adic` supplies trace values, while full characteristic-polynomial equality also needs determinant equality. That must come from the cyclotomic determinant or another explicit provider.

- **Topology:** `T2Space A` is load-bearing for extending equality from a dense set. `AlgebraicClosure ℚ_[p]` supplies it via its normed-field topology. No polynomial topology should be introduced.

- **Normalization:** The repository uses arithmetic Frobenius. Replacing it with its inverse is not harmless because characteristic polynomials of an element and its inverse need not coincide.

- **Conclusion:** Brauer–Nesbitt yields `Nonempty (Representation.Equiv …)`, not literal equality of `GaloisRep`s. The graph name `equal_of_charFrob_eq` should therefore be replaced.

## 5. T2 versus T3

Only a witness of:

```lean
RatArithmeticFrobeniusConjugacyDensity
```

may eventually be a named T2 historical assumption. Even that is **not currently authorized**: the control policy prohibits a T2 assumption until its exact Lean type and primary-source locator have been independently reviewed, while `SRC-003` is only the blueprint route, not an exact Chebotarev source locator. [historical-assumptions.ndjson](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/control/historical-assumptions.ndjson:1), [SOURCE-REGISTER.md](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/SOURCE-REGISTER.md:11)

At T2:

- Density may be exactly one authorized custom axiom after the source and operator gates.
- D0–D1 and A0–A5 must remain ordinary standard-trio proofs.
- No “compatible-family comparison” or representation-equivalence axiom is admissible.

At T3:

- The density witness itself must be proved with `[propext, Classical.choice, Quot.sound]`.
- The complete consumer closure must contain no custom density axiom or `sorryAx`.

The current graph row should therefore be split into a pure density provider and standard-trio adapters. [proof-obligations.ndjson](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/control/proof-obligations.ndjson:29)

## 6. Build plan and stop-loss conditions

1. Add only D0–D1 and A0–A3 first. Target-build and individually audit every declaration.
2. Add A4 and A5 with density as an explicit argument. Confirm the exact standard trio.
3. Add F0, without changing `GaloisRepFamily.isCompatible`.
4. For the `ℚ`, fixed-`p`, fixed-`φ` consumer, combine `S` with the unique `p`-place using `Rat.HeightOneSpectrum.primesEquiv`; prove the family’s `(p : 𝓞 ℚ) ∉ v.asIdeal` side condition.
5. Freeze D2 as the exact missing contract. Do not register an axiom until an exact primary-source locator and operator authorization exist.
6. Only then add the consumer-specific model, determinant equality, semisimplicity, and same-coefficient characteristic-polynomial comparison.

Stop immediately if:

- density is claimed for unsaturated chosen representatives;
- the produced finite-Chebotarev theorem uses a different global Frobenius and no conjugacy bridge is proved;
- different coefficient fields or embeddings are compared without explicit transport;
- only trace equality is available;
- family compatibility is treated as semisimplicity;
- a finite exceptional condition remains a cofinite slogan rather than an exact `Finset`;
- the conclusion is literal representation equality;
- any adapter acquires a custom axiom or `sorryAx`;
- the T2 source locator remains absent.

This is a viable bounded implementation slice, but `FLT-CHEBOTAREV`, the compatible-family terminal, and FLT remain unproved.

