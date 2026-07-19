# THM-TAME-FIXED-FIELD-UNIFORMIZER independent literature review

## Review identity and scope

- Reviewer model: `claude-opus-4-8`
- Role: independent literature and proof-design gate
- Mode: read-only
- Reviewed target: `FixedFieldUniformizerDecomposition`
- Reviewed source: SRC-026, J. Neukirch, *Algebraic Number Theory*
- Source SHA-256: `a6d883b38fa7adc661248219d8611cc18dd22a1e6dd4ac3646be0aa6e6f4607c`

## Verdict

**PASS — bounded literature gate only.**

The reviewer independently inspected and confirmed all three cited source locations:

- printed pp. 120--121, PDF pp. 139--140: normalized discrete uniformizer decomposition;
- printed p. 154, PDF p. 173: the maximal unramified subextension has the base value group; and
- printed p. 173, PDF p. 192: the inertia fixed field is the maximal unramified extension in the
  henselian/separable-closure case.

The PDF hash matched the source-register pin.

## Hypothesis and representation findings

The reviewer found the source-to-Lean translation faithful:

- the completed local field is henselian;
- in the characteristic-zero setting the chosen algebraic closure supplies the needed separable
  closure;
- a residual factor of value zero gives both the factor and its inverse integral;
- the sign of the multiplicative valuation is only a normalization detail because the exponent is
  quantified over `ℤ`; and
- fixedness of the residual factor follows from fixed-field closure and the base uniformizer being
  fixed.

The reviewer confirmed that the repository does not currently expose the necessary theorem taking
membership in `IntermediateField.fixedField (localInertiaGroup v)` to equality with the base value
group. The packet therefore does not overclaim available Lean infrastructure.

## Control-data findings

- `literature_status = exact` is justified.
- `proof_status = stated` remains honest: the target proposition is consumed as a hypothesis and is
  not proved.
- The changed NDJSON was valid and no unrelated theorem status was altered.
- The counterexample audit is material: ramified extensions can enlarge the value group, and
  one-sided integrality is insufficient for the downstream Kummer construction.

## Non-closure statement

This PASS does **not** prove `FixedFieldUniformizerDecomposition`, does **not** close
`FLT-TAME-RESIDUE`, and does **not** authorize promotion of the conditional downstream wrappers.

## Recommended next gate

Build and independently review the fixed-field/value-group bridge first. Only after that bridge is
kernel-clean should a second bounded cycle assemble the uniformizer power and integral unit.
