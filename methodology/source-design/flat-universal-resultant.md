# THM-FLAT-RESULTANT reclassification and design packet

## Adjudication

`WeierstrassCurve.resultant_Φ_ΨSq` is an **exact-sourced, high-difficulty optional
strengthening**. It is not a low-difficulty direct application of the existing polynomial API, and
it is no longer on the FLT completion critical path.

The reviewed theorem `WeierstrassCurve.isCoprime_Φ_ΨSq` has a kernel-clean maximal-ideal/field proof
that does not consume the admitted resultant. The finite-flat good-reduction theorem also needs a
group-scheme/Hopf-algebra construction and a local/global torsion bridge; the universal resultant
does not supply either. Accordingly:

- `required_for_completion` changes from `true` to `false`;
- `critical_path` changes from `true` to `false`;
- `unlocks` changes from `2` to `0`;
- `THM-FLAT-GOOD-REDUCTION` no longer lists this theorem as a dependency; and
- the admission remains visible and may be removed in a later repository-wide theorem-cleanup
  programme.

This is a dependency correction, not a proof claim and not deletion of the theorem.

## Exact literature

SRC-027 is Harry Schmidt, *Resultants and discriminants of multiplication polynomials for elliptic
curves*, Journal of Number Theory 149 (2015), 70--91, available from the
[University of Basel repository](https://edoc.unibas.ch/server/api/core/bitstreams/ae661a6a-064c-42ef-8c75-fee3719e5c05/content).
The inspected PDF SHA-256 is
`5b738265ea3a454721166cc0787426786cdd5292d67bc25dcd3ba46d37c06799`.

- Theorem 1.1, printed p. 2, proves the resultant formula for the normalized multiplication
  polynomials of a short Weierstrass equation.
- The discussion on printed pp. 3--4 explains that the formulas are polynomial identities and
  survive specialization.
- Section 8, printed pp. 14--15, transports the formula to the general Tate/Weierstrass equation;
  identity (43) is the exact discriminant-power form needed here.

The old `Flat.lean` docstring cites Ayad 1992 only as a short-Weierstrass reference. SRC-027 is the
more direct exact source: it states the resultant formula and explicitly performs the passage to the
general Weierstrass form.

## Statement comparison

| Source | Lean target | Formal residual |
|---|---|---|
| Natural `n ≥ 2` | Integer `n ≠ 0` | Prove the `n = ±1` base cases and reduce negative indices to `natAbs`. |
| Normalized multiplication numerator `A_n^T` | `W.Φ n` | Prove exact equality under Mathlib's normalization. |
| Normalized multiplication denominator `B_n^T` | `W.ΨSq n` | Prove exact equality, including formal padded degree `n²-1`. |
| Universal general Weierstrass coefficients | Arbitrary `CommRing R₀` and `W : WeierstrassCurve R₀` | Construct the universal curve and specialize by its coefficient map. |
| `res(A_n^T,B_n^T)=Δ^κ` | Target permits `+Δ^κ` or `-Δ^κ` | The Lean conclusion is weaker on sign, so a convention sign mismatch is harmless after the polynomial identification. |

The already proved `resultant_Φ_ΨSq_explicit_eq_default` closes only the explicit-degree padding
question. It does not prove the universal resultant identity.

## Why the original estimate was wrong

The existing resultant API computes and transports resultants, but no library theorem supplies this
elliptic-curve identity. Schmidt's proof is not a routine determinant simplification: it establishes
the universal shape, determines the exponent and constant, and uses elliptic/modular analytic
calculations, followed by a general-Weierstrass transport. A complete Lean development would need
either that machinery or a new purely algebraic recurrence proof.

The contract is therefore re-estimated from difficulty 4 to difficulty 9, with low confidence and a
p50 budget of 900,000 tokens / 120 active hours. This estimate must be revised from build evidence,
not optimism, if the theorem is resumed.

## Deferred sublemma graph

### R0 — statement and convention layer

1. Prove `Φ` and `ΨSq` are invariant under sign of the integer index in the exact required form.
2. Close `n = 1` and `n = -1` by simplification.
3. Define the universal general Weierstrass curve over
   `ℤ[a₁,a₂,a₃,a₄,a₆]` in a representation compatible with Mathlib.
4. **Crux:** prove Mathlib `Φ/ΨSq` equal Schmidt's normalized multiplication
   numerator/denominator. Treat this as its own bounded adapter task with exact low-index tests and
   a base-change audit before attempting the universal identity.
5. Prove specialization/base-change compatibility for both polynomials and the resultant.

R0 is the first bounded build tranche. A failure here stops the work before any large proof attempt.

### R1 — universal resultant core

The first design candidate should be Schmidt's source-faithful arithmetic route in §2 and §8. The
Lean target permits either sign, so the proof only needs the source's up-to-sign determination: show
the universal resultant has discriminant-power shape, determine the exponent by weights, and use
the integral Tate form plus field-level coprimality in characteristics 2 and 3 to eliminate unwanted
prime factors. This avoids formalizing the Fourier calculation used to determine the exact positive
sign.

Retain the following alternatives and choose only after a separate design comparison:

- **Full source route:** formalize the modular/Fourier calculation if an exact-sign strengthening is
  later desired. This is unnecessary for the current disjunctive target.
- **Algebraic recurrence route:** locate and verify a source giving a recurrence for resultants of
  the exact multiplication-polynomial normalization, then formalize the recurrence by induction.
  This may be smaller, but no such exact compatible route has yet passed source review.

The source theorem may guide the proof but cannot be introduced as a custom axiom under the T1
policy.

### R2 — specialization and public theorem

1. Specialize the universal equality to arbitrary `R₀` and `W`.
2. Reconcile default and explicit padded resultants using the already kernel-clean normalization
   theorem.
3. Assemble positive, negative, and base cases.
4. Run a targeted build and fresh `#print axioms` audit.
5. Obtain independent mathematical and Lean review before changing `proof_status`.

## Counterexample and scope audit

- Nonvanishing/coprimality over nonsingular fibres proves only that the resultant is a unit there;
  it does not determine the exact discriminant power or its coefficient.
- Checking finitely many values of `n` cannot prove the universally quantified identity.
- A short-Weierstrass proof over fields of characteristic not 2 or 3 cannot simply be specialized
  to arbitrary commutative rings; SRC-027's universal Tate-form passage or an equivalent integral
  argument is essential.
- The stronger identity is not a surrogate for finite-flat group-scheme or point-specialization
  infrastructure.

## Next gate

Do not schedule R0 while dependency-ready critical-path theorems remain. If the optional cleanup is
resumed, split R0.4 into the first bounded GPT-5.6 xhigh build and send the resulting convention
adapter to Fable, with Claude Opus 4.8 as the fallback reviewer.
