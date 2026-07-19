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

## Independent review

- Reviewer: Claude Opus 4.8, operating in a separate read-only process
- Frozen candidate: `4aa059b2ddd65e2cb815ffd580be1ad9a28ca9b9`
- Review result: **PASS**
- Review session: `c96781d9-e5b9-4537-9e83-fd86bcde15d5`

The reviewer independently rebuilt the frozen candidate (`3443/3443`, exit code `0`), confirmed
that both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, and found no
`sorry`, `admit`, `native_decide`, or custom axiom in the target module. The mathematical review
confirmed the maximal-ideal stability argument, conjugation proof of inertia normality, and the
closed-subgroup use of `InfiniteGalois.normal_iff_isGalois`. It also confirmed that the module is
strictly downstream of `AbsoluteGaloisGroup` and does not assume any of the open value-group,
uniformizer, tame-residue, or FLT conclusions.

The reviewer did not independently re-fetch and hash the Neukirch source; that assurance remains
the separately recorded literature gate. Fable 5 was attempted first but returned an out-of-usage-
credits error, so the declared Opus 4.8 capacity fallback was used. No same-family GPT review is
being represented as independent review.
