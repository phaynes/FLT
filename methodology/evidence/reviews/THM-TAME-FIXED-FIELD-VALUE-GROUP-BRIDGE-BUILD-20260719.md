# THM-TAME-FIXED-FIELD value-group bridge build checkpoint

## Scope

- Task: `task:ca-flt-tame-fixed-field-value-group-bridge-20260719`
- Producer: GPT-5.6 xhigh build lane
- Module: `FLTMethodology.Probes.FixedFieldValueGroupBridge`
- Bounded claim: normality of local inertia and Galoisness of its fixed field

## Fresh build and axiom evidence

Command:

```text
lake build FLTMethodology.Probes.FixedFieldValueGroupBridge
```

Result: exit code `0`; `3443/3443` targets built.

The module executes:

```text
#print axioms IsDedekindDomain.HeightOneSpectrum.localInertiaGroup_normal
#print axioms IsDedekindDomain.HeightOneSpectrum.fixedField_localInertia_isGalois
```

Both declarations depend only on:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` or custom axiom appears.

## What was proved

- The unique maximal ideal of `IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ` is stable under every absolute Galois
  automorphism.
- Conjugation therefore preserves the subgroup acting trivially modulo that maximal ideal, giving
  `(localInertiaGroup v).Normal`.
- Existing closedness plus `InfiniteGalois.normal_iff_isGalois` gives
  `IsGalois Kᵥ (IntermediateField.fixedField (localInertiaGroup v))`.

## Explicit non-closure

This checkpoint does not prove that the fixed field is unramified, that its value group equals the
base value group, the uniformizer-power decomposition, `FixedFieldUniformizerDecomposition`,
`FLT-TAME-RESIDUE`, or FLT. The next formal boundary is the finite-subextension inertia and
ramification-index-one bridge to `HeightOneSpectrum.valuation_liesOver`.
