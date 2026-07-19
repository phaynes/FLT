# THM-TAME-FIXED-FIELD-UNIFORMIZER source and design packet

## Gate result

**Literature gate: PASS. Lean proof gate: OPEN.**

The exact mathematical result required by `FixedFieldUniformizerDecomposition` is covered by the
three linked results in SRC-026. The checked source is Jürgen Neukirch, *Algebraic Number Theory*,
available from the [University of California, Santa Barbara](https://web.math.ucsb.edu/~agboola/teaching/2021/fall/225A/neukirch.pdf).
The inspected PDF has SHA-256
`a6d883b38fa7adc661248219d8611cc18dd22a1e6dd4ac3646be0aa6e6f4607c`.

This packet does not claim that the Lean theorem is proved. The repository does not currently
contain a theorem identifying the value group of
`IntermediateField.fixedField (localInertiaGroup v)` with the base value group. That is the main
technical bridge still to construct.

## Exact Lean target

The target in `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` says that for every
nonzero `u : Kᵥᵃˡᵍ` fixed by `localInertiaGroup v`, there are `m : ℤ` and `a : Kᵥᵃˡᵍ` such that:

- `a` and `a⁻¹` are integral over `𝒪ᵥ`;
- `a` is fixed by local inertia; and
- `u = algebraMap Kᵥ Kᵥᵃˡᵍ (tameUniformizer v) ^ m * a`.

## Exact source chain

| Source fact | Exact locator | Use in the Lean target |
|---|---|---|
| In a normalized discretely valued field every nonzero element has a unique expression `x = unit * π^m`, with `m : ℤ`. | SRC-026, Chapter II §3, Proposition 3.8 and the paragraph immediately following it, printed pp. 120--121, PDF pp. 139--140. | Converts an integer-valued valuation into the required uniformizer-power/unit decomposition. |
| The maximal unramified subextension has the same value group as the base field. | SRC-026, Chapter II §7, Definition 7.4 and Proposition 7.5, printed p. 154, PDF p. 173. | Ensures that the valuation of a fixed-field element is an integer multiple of the chosen base uniformizer valuation. |
| The fixed field of inertia is the maximal unramified subextension; for a henselian field in a separable closure it is the maximal unramified extension. | SRC-026, Chapter II §9, Definition 9.10 and Proposition 9.11, printed p. 173, PDF p. 192. | Identifies the repository's fixed-field hypothesis with the field to which Proposition 7.5 applies. |

The nearby Wiese notes (SRC-019, §3.2) independently corroborate the terminology and describe the
inertia fixed field as `K^unr`, but they are not needed to mark this exact source gate complete.

## Hypothesis translation

| Mathematical hypothesis | Repository representation | Status |
|---|---|---|
| Complete discretely valued base field, hence henselian | `Kᵥ`, the adic completion at `v`; `tameUniformizer_valuation` fixes its normalized multiplicative value | Existing |
| Chosen algebraic/separable closure | `Kᵥᵃˡᵍ` | Existing |
| Inertia subgroup | `localInertiaGroup v`, defined from the maximal ideal of `IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ` | Existing definition; equivalence with Neukirch's inertia-field setup needs a formal bridge |
| Inertia fixed field | `IntermediateField.fixedField (localInertiaGroup v)` | Existing |
| Maximal unramified extension has the base value group | No matching repository or pinned-Mathlib theorem found | **Open bridge** |
| Valuation-ring unit iff value zero/one | `ValuationSubring.isUnit_iff_valued_eq_one`; local spectral-norm integrality lemmas | Existing for represented valuation rings, but must be connected to the fixed field |
| Uniformizer power times unit decomposition | `eq_pow_uniformizer_mul_unit` in `FLT/DedekindDomain/AdicValuation.lean` | Existing only for nonzero integral elements of the base finite adic completion; not directly reusable for arbitrary elements of the infinite inertia fixed field |

## Mathematical derivation

Write `T` for the inertia fixed field in `Kᵥᵃˡᵍ` and `π` for the image of
`tameUniformizer v`. SRC-026 identifies `T` with the maximal unramified extension and proves
`v(T×) = v(Kᵥ×)`. Therefore, for nonzero `u ∈ T`, choose `m : ℤ` with
`v(u) = v(π^m)` and set `a = π^(-m) * u`. Then `v(a) = 0`. Hence `a` is a
valuation-ring unit, equivalently both `a` and `a⁻¹` lie in the valuation ring and are integral
over `𝒪ᵥ`. Both `u` and `π` are inertia-fixed, so `a` is inertia-fixed. Rearranging gives
`u = π^m * a`.

The sign of `m` must be checked against the repository convention
`Valued.v (tameUniformizer v) = Multiplicative.ofAdd (-1 : ℤ)`. The contract quantifies over all
integers, so this is a normalization detail rather than a statement mismatch.

## Proposed Lean sublemma graph

1. `fixedField_localInertia_eq_maximalUnramified` or a weaker purpose-built theorem connecting
   membership in the fixed field to the unramified value-group result.
2. `exists_int_valuation_eq_uniformizer_zpow` for nonzero fixed-field elements.
3. Define `a := (algebraMap Kᵥ Kᵥᵃˡᵍ (tameUniformizer v)) ^ (-m) * u`.
4. Prove the represented valuation/spectral norm of `a` and `a⁻¹` is at most one, then use
   `isIntegral_of_spectralNorm_le_one` and `spectralNorm_inv`.
5. Prove fixed-field membership using closure under algebra-mapped base elements, powers,
   products, and inverses.
6. Normalize the integer-power algebra to the target equality.

A purpose-built value-group bridge is preferable to introducing an opaque `Prop` provider. If a
general maximal-unramified-extension theory is added, it should expose a reusable theorem about
the restricted valuation or value-group map and be independently reviewed before this consumer is
closed.

## Library survey and residual technical risk

The targeted repository and vendored-Mathlib search found valuation/value-group infrastructure,
including `valueGroupOrderIso₀`, restriction lemmas, `ValuationSubring.isUnit_iff_valued_eq_one`,
and `eq_pow_uniformizer_mul_unit`. It found no existing maximal-unramified-extension object or
theorem relating `localInertiaGroup`'s fixed field to an unchanged value group. Consequently:

- the source and statement risks are closed;
- the formal representation risk remains high;
- the first build task should be the fixed-field/value-group bridge, not an attempted one-shot proof
  of the final declaration; and
- no aggregate class-field or tame-residue closure may be inferred from this literature result.

## Counterexample and weakening review

The source chain depends essentially on the fixed field being the maximal **unramified** extension.
For a ramified algebraic extension the value group can enlarge, so a base uniformizer need not
generate all element values with integer exponents. Likewise, proving only that `a` is integral is
insufficient: the downstream Kummer construction requires `a⁻¹` integral as well. The proposed
bridge must therefore establish value zero (unit status), not merely nonnegative value.

## Next gate

Run a bounded GPT-5.6 xhigh design/build cycle for the fixed-field/value-group bridge. Its output
must include targeted builds, a fresh axiom audit, and an explicit residual-gap report. Independent
review is assigned to Fable, with Claude Opus 4.8 as the declared fallback if Fable is unavailable.
