# Fable 5 independent name-source design — quaternion boundary

- Pipeline stage: `tri-design-axiomatise / name-source`
- Component difficulty: 6
- Model: `claude-fable-5`
- Transport result: success
- Granted budget: 1800 seconds under the superseded flat pre-contract policy
- Actual elapsed: 542735 ms
- Token telemetry: 8967 input, 99094 cache creation, 1055863 cache read, 36115 output
- Verdict: **REVISE**

The first 600-second Fable attempt timed out and is separately recorded as `TIMEOUT / NO VERDICT`.
This successful attempt completed before the operator introduced the scaled timeout contract. Its
content verdict is retained; it does not by itself promote the component through the three-design or
agreement gates.

## 1. Current consumer boundary

The exact consumer is
`TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ` in
`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`:

```lean
instance isFiniteRelIndex_Δ [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex 𝓕ˣ (ℒ.Δ D g) := by knownin1980s
```

Here `𝓕ˣ` is the range of finite-adele scalar units, and `ℒ.Δ D g` is the intersection of the
level-plus-central-scalar subgroup with the conjugated quaternion-unit range. Its direct consumers
are the Petersson inner-product construction and concrete Hecke-operator sufficient-smallness path,
which feed `FLT-SUPPORT-AUTOMORPHIC`.

## 2. Primary source finding

The mathematical statement is the classical finiteness of
`(U · A_f^× ∩ g⁻¹D^×g) / F^×` for a totally real field, a totally definite quaternion algebra,
compact-open level `U`, and finite-adelic `g`.

The repository currently registers exact locators only to Voight 2021, a modern secondary source,
and neither cited lemma states the exact adelic bridge. Plausible primary sources are Eichler,
Crelle 195 (1955/56), Shimizu, Annals of Mathematics 81 (1965), and Vignéras, LNM 800 (1980), but
the repository does not yet contain a verified page-and-theorem locator. Fable therefore reports a
**SOURCE GAP** rather than inventing a citation.

## 3. Proposed minimal T2 interface

Fable proposes stripping the irrelevant `LevelStruct` coefficient ring and character data and
naming the exact adelic stabilizer theorem:

```lean
axiom TotallyDefiniteQuaternionAlgebra.isFiniteRelIndex_stabilizer_statement
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] [WithRigidification F D]
    (U : Subgroup GL₂(𝔸ᶠ[F]))
    (hUc : IsCompact (X := GL₂(𝔸ᶠ[F])) U) (hUo : IsOpen (X := GL₂(𝔸ᶠ[F])) U)
    (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex
      (MonoidHom.range (Units.map (algebraMap F M₂(𝔸ᶠ[F])).toMonoidHom))
      ((U ⊔ MonoidHom.range
          (Units.map (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])).toMonoidHom)) ⊓
        toConjAct g⁻¹ • MonoidHom.range (WithRigidification.unitsIncl F D))
```

The consumer would apply it at `U := ℒ.U`. The already kernel-clean finite-quotient-model adapter is
intentionally not part of this T2 assumption; that adapter belongs to a future T3 proof route.

Fable rejected three broader boundaries: an axiom over the full `LevelStruct`, a Voight order-unit
lemma bundled with unsourced adelic bridges, and an existential `IntegralStabilizerModel` assumption
that would merely hide the open sublemma graph.

## 4. Counterexample checks

The review explicitly retained these stop-loss checks:

- The proposed direct injection into norm-one units fails without a reduced-norm square-class
  condition. The correct finite quotient is by order units modulo base-field integer units.
- Compactness does not imply finiteness; compact profinite matrix groups are generally infinite.
- The level subgroup enlarged by the finite idelic centre is not compact.
- A conjugated maximal compact need not lie in the un-conjugated integral matrix group, so a
  `g = 1` theorem is too weak for Hecke operators.
- Finiteness of a double-coset space does not imply finiteness of each stabilizer quotient.

## 5. Axiom surface and probe plan

The expected path is the named axiom to `isFiniteRelIndex_Δ`, then the inner-product and Hecke
consumers, then the automorphic support cluster and the top theorem. The intended T2 closure is the
new exact axiom plus `propext`, `Classical.choice`, and `Quot.sound`, with generic `knownin1980s`
removed from this path.

The exact signature has not yet been elaborated. The required next probe imports the quaternion
basic module, declares a temporary copy of the signature, proves the exact existing instance goal by
application at `ℒ.U`, and audits the probe declaration's axioms.

## 6. Verdict

**REVISE.** The signature is a plausible minimal T2 boundary and is expected to discharge the real
consumer without hiding the order-construction work. It is not yet `NAMEABLE`: first register an
exact primary pre-1990 source locator and run the signature/application axiom probe. No T2 axiom was
registered and no T3 proof was claimed.
