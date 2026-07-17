# Opus 4.8 primary design — quaternion boundary

- Component: `quaternion-boundary`
- Obligation: `FLT-HIST-QUATERNION`
- Stage: primary T2 name-source design
- Agent: `opus48-primary-designer-d6`
- Backend/model: `claude-code` / `claude-opus-4-8`
- Permission mode: `suggest` (read-only requested)
- Scheduled difficulty/budget: `6` / `2400s`
- Transport result: `SUCCESS`
- Actual elapsed: `428147ms` (`real 428.12s` from `/usr/bin/time`)
- Claude session: `89163dc2-3aa2-49ce-bb25-7ae9262b90ab`
- Unique request IDs: `16`
- Token telemetry, deduplicated by `requestId`: `8560` input, `67611` cache creation,
  `664452` cache read, `26924` output (`767547` total including cache tokens)
- Verdict: **REVISE**
- Promotion: none; GPT review and the human axiomatization gate remain mandatory

The bridge's final response summarized the report and pointed to Claude's automatically generated
plan cache. The complete report below is preserved from that cache so the authorized repository
artifact contains the full model deliverable. The model made no FLT repository edits.

Deduplicated request IDs:

```text
req_011Cd7ExMW3Fu5gFhM4JzcBj
req_011Cd7ExftaftURxdxKQyxWj
req_011Cd7EyBHABkkMKAx5sfqEY
req_011Cd7EyUnNFZoj21MNpLPiS
req_011Cd7EzDkWkCLiVR1cDKfkJ
req_011Cd7F19Y3Hv4BpBcLHu2Ys
req_011Cd7F2Mh4SoAXguaRZ3JoJ
req_011Cd7F32g6dSxt3WC9nRBLv
req_011Cd7F3JYq182gLvo7KDSUP
req_011Cd7F3jPZYtoJi3Yfex2fU
req_011Cd7F4Wf7u5JAqwdoPf8yf
req_011Cd7F5EAi9ahzj4MyL26G1
req_011Cd7F5xygFrVjgU5fyfD45
req_011Cd7FFt3JUBdBcfw3cneRm
req_011Cd7FGTBMCt6pu5k7uUgGi
req_011Cd7FU8eDUnoMQnwKwK53M
```

## Context

This is a Stage-1 **name-source design** deliverable, not a code change. Under the Opus-first
producer ladder I am the first-attempt primary producer for component `quaternion-boundary`,
obligation `FLT-HIST-QUATERNION`, target assurance **T2** (named historical interface — *not* T3
proof discharge). I worked read-only, registered no axiom, and treat no citation or scaffold as a
proof. The output is the 8-section report required by
`methodology/review/flt-completion/quaternion-boundary/stage-1-prompt-gpt56xhigh.md`, with the
Opus-ladder additions: reconcile Fable's `REVISE`, verify/reject Fable's stabilizer signature, and
find a page-exact primary locator if supportable.

**Bottom line:** Fable's signature is **VERIFIED sound** (I accept it, with refinements). The sole
blocker to `NAMEABLE` is an unclosed **SOURCE GAP** — no page-exact pre-1990 primary locator exists
in the repository and I will not invent one. Verdict: **REVISE** (concurs with Fable, strengthened).
Difficulty-6; a later human source-verification gate is required regardless.

## 1. CURRENT CONSUMER BOUNDARY

**Declaration** (`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean:496–499`), an `instance`:

```lean
@[nolint unusedArguments]
instance isFiniteRelIndex_Δ [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex 𝓕ˣ (ℒ.Δ D g) := by
  knownin1980s
```

Ambient section variables (lines 72–77):
`(F : Type*) [Field F] [NumberField F]`; `(D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]`;
plus the instance-local `[NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
[IsQuaternionAlgebra.IsTotallyDefinite F D]`, and `(R : Type*)` carried by `LevelStruct F R`.

**Notation expansions (verified against `Basic.lean:83–87`, `412`, `475`):**

- `𝓕ˣ` := `MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F]))))` — image of `Fˣ`.
- `𝔸ˣ F` := `MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F]))))` — the finite-idelic centre; `≤ center` (line 90).
- `𝓓ˣ` := `MonoidHom.range (WithRigidification.unitsIncl F D)` — image of `Dˣ` via the rigidification `D ↪ M₂(𝔸ᶠ)`.
- `ℒ.UA` := `ℒ.U ⊔ 𝔸ˣ F` (line 412; `isOpen_UA` proved, **not compact**).
- `ℒ.Δ D g` := `ℒ.UA ⊓ toConjAct g⁻¹ • 𝓓ˣ` (line 475). So
  `Δ = (ℒ.U ⊔ 𝔸ˣ F) ⊓ toConjAct g⁻¹ • 𝓓ˣ`.
- `Fscalar` (source-design doc) = `𝓕ˣ`; scalar containment `𝓕ˣ ≤ ℒ.Δ D g` is **proved**:
  `LevelStruct.range_units_le_range` (lines 478–485). This is the already-discharged easy half.

**Body:** `knownin1980s` = the global `axiom knownin1980s {P : Prop} : P`
(`FLT/Assumptions/KnownIn1980s.lean:79`, tactic macro line 100). Generic Prop-inhabiting authority.

**Direct consumers / top-dependency paths that inherit the named axiom:**

- `InnerProduct.lean:154` — `have := ℒ.isFiniteRelIndex_Δ (D := D)` inside
  `LevelStruct.sum_filter_map_eq_ΔIndex_div_ΔIndex` and the Petersson/Haar `relIndex` machinery.
- `HeckeOperators/Concrete.lean:596` — `(U₁ 𝒮).toStruct.isFiniteRelIndex_Δ (D := D) g` inside
  `coprime_ΔIndex` (concrete Hecke sufficient-smallness path).
- `Basic.lean:512 ΔIndex` (well-definedness on double cosets) and `InnerProduct` both use that the
  relative index is finite/nonzero; `ΔIndex_mul_relIndex` (line 1009) also depends on it.

These feed the automorphic-support cluster `FLT-SUPPORT-AUTOMORPHIC` (obligation row 48:
`direct_dependencies:["FLT-HIST-QUATERNION"]`, `graph_depth:1`, `critical_path:true`).

## 2. PRIMARY SOURCE LOCATOR — SOURCE GAP

**The mathematical statement to be named:** for a totally real `F`, a totally definite quaternion
algebra `D/F`, a compact-open level `U ⊆ GL₂(𝔸ᶠ)`, and `g ∈ GL₂(𝔸ᶠ)`, the group
`(U·𝔸ᶠˣ ∩ g⁻¹Dˣg)/Fˣ` is finite (equivalently `IsFiniteRelIndex 𝓕ˣ (Δ_g)`).

**Repository evidence:** only **Voight 2021** is registered:

- **SRC-017** — Voight, *Quaternion Algebras*, GTM 288 (2021), **Lemma 17.7.13**: the norm-one unit
  group `𝒪¹` of an order in a totally definite quaternion algebra is finite. It proves only the
  norm-one terminal and does not justify the docstring's scalar-quotient-to-`𝒪¹` injection.
- **SRC-022** — Voight (2021), **Lemma 26.5.1**: `𝒪ˣ/Rˣ` is finite for an order `𝒪` over number
  ring `R`, via the norm map, finiteness of `𝒪¹`, and the finite square-class quotient `Rˣ/(Rˣ)²`.
  This is the correct finite target, but the compact-open-to-order construction and injection into
  it remain unsourced and unformalized.

Two independent reasons make this a source gap for a T2 historical name:

1. Voight 2021 is a modern secondary monograph, not a pre-1990 primary source.
2. Neither Voight lemma states the missing adelic-to-order bridge: compact-open containment in a
   conjugated integral lattice, construction of the resulting order, and the quotient injection
   with exact kernel.

Candidate primary sources, all **UNVERIFIED** and therefore only human-gate leads, are Shimizu's
*On zeta functions of quaternion algebras* (Annals of Mathematics 81, 1965), Eichler's 1955/56
quaternion-arithmetic work in Crelle 195, and Vignéras, LNM 800 (1980), Chapter V. No page or theorem
number was asserted without a checked primary scan.

## 3. MINIMAL NAMED T2 INTERFACE

Canonical name: `TotallyDefiniteQuaternionAlgebra.isFiniteRelIndex_stabilizer`.

```lean
axiom TotallyDefiniteQuaternionAlgebra.isFiniteRelIndex_stabilizer
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (U : Subgroup GL₂(𝔸ᶠ[F]))
    (hUc : IsCompact (X := GL₂(𝔸ᶠ[F])) U) (hUo : IsOpen (X := GL₂(𝔸ᶠ[F])) U)
    (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex
      (MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F])))))
      ((U ⊔ MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F]))))) ⊓
        toConjAct g⁻¹ • MonoidHom.range (WithRigidification.unitsIncl F D))
```

The signature matches the repository notation and applying it at `U := ℒ.U`,
`hUc := ℒ.isCompact_U`, `hUo := ℒ.isOpen_U`, and `g := g` gives the exact consumer by unfolding
`UA` and `Δ`. It strips only irrelevant `LevelStruct` coefficient/character data. It contains no
generic `Prop` and does not bundle the existing finite-quotient adapter or future T3 construction.

Existing kernel-clean declarations kept outside the axiom are
`LevelStruct.range_units_le_range` and
`FLT.Components.QuaternionRelativeIndex.isFiniteRelIndex_of_finite_quotient_model`.

## 4. MINIMALITY AND SOURCE FAITHFULNESS

- The finiteness content is classical pre-1990 quaternion arithmetic, even though the exact primary
  locator is not yet verified.
- `IsTotallyReal F` and total definiteness are load-bearing; without them order-unit groups can be
  infinite. Compactness and openness of `U` are required; taking `U = ⊤` invalidates the result.
- `g` must remain arbitrary because conjugation moves the integral lattice and direct consumers use
  arbitrary Hecke representatives.
- The conclusion asserts only the finite relative index already required. It does not assert the
  false norm-one injection, construct an order, bound the index, or expose unrelated facts.
- What remains unnameable is an honest page-exact pre-1990 citation for the adelic bridge.

## 5. DEPENDENCY AND AXIOM-SURFACE PATH

```text
isFiniteRelIndex_stabilizer (new named T2 boundary)
        |
        v
LevelStruct.isFiniteRelIndex_Δ
        +--> LevelStruct.ΔIndex / ΔIndex_mul_relIndex
        +--> InnerProduct Petersson/relative-index chain
        +--> HeckeOperators.Concrete.coprime_ΔIndex
                    |
                    v
        FLT-SUPPORT-AUTOMORPHIC and reached exports
```

After replacement, reached declarations should name the new axiom plus the standard three in their
`#print axioms` output; generic `knownin1980s` should disappear from this path. The finite-quotient
adapter, scalar-containment lemma, and unrelated Mazur path should remain unaffected.

## 6. COUNTEREXAMPLES AND OVERSTATEMENT RISKS

- The direct map `Δ_g/Fˣ -> 𝒪¹` fails unless the reduced-norm class is a square. The correct target
  is `𝒪ˣ/(𝒪_F)ˣ`.
- Compactness does not imply finiteness; compact profinite matrix groups can be infinite.
- `UA = U ⊔ 𝔸ᶠˣ` contains the finite-idelic centre and is generally not compact.
- Conjugation by `g` changes the integral lattice, so an un-conjugated or `g = 1` order is inadequate.
- Finite double-coset type does not imply each stabilizer quotient is finite; cocompactness likewise
  does not supply the required finite quotient.

## 7. SIGNATURE PROBE PLAN — NOT RUN

The exact signature has not been elaboration-tested. The proposed outside-repository probe is:

```lean
import FLT.AutomorphicForm.QuaternionAlgebra.Basic
open TotallyDefiniteQuaternionAlgebra WeightTwoAutomorphicForm

axiom isFiniteRelIndex_stabilizer_PROBE
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (U : Subgroup GL₂(𝔸ᶠ[F])) (hUc : IsCompact (X := GL₂(𝔸ᶠ[F])) U)
    (hUo : IsOpen (X := GL₂(𝔸ᶠ[F])) U) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex
      (MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F])))))
      ((U ⊔ MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F]))))) ⊓
        toConjAct g⁻¹ • MonoidHom.range (WithRigidification.unitsIncl F D))

#check @isFiniteRelIndex_stabilizer_PROBE

example {F} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {D} [Ring D] [Algebra F D] [WithRigidification F D]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D]
    {R} (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex _ (ℒ.Δ D g) :=
  isFiniteRelIndex_stabilizer_PROBE F D ℒ.U ℒ.isCompact_U ℒ.isOpen_U g

#print axioms isFiniteRelIndex_stabilizer_PROBE
```

Passing the application is the gate from inspection-only to elaboration-verified signature.

## 8. VERDICT — REVISE

Fable's stabilizer signature is accepted as sound, minimal, and capable of discharging the consumer
by application, modulo the un-run elaboration probe. The component is not
`READY-FOR-GPT-REVIEW`: the mandatory page-exact pre-1990 source for the adelic bridge is a genuine
source gap. The two exact revision steps are to run the signature/application probe and have the
human source-verification gate confirm a primary locator. No axiom is registered and no T3 proof is
claimed.
