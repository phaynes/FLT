# Literature-assisted proof design delta, 2026-07-19

## Purpose

This document turns the adjudicated parts of the supplied literature review into
bounded Lean-construction aids. It deliberately stops short of speculative Lean
signatures where the primary theorem or repository vocabulary is not exact.

Every item below has `may_promote = false`. A design item becomes executable only when
its source gate and vocabulary gate both pass. Existing proof-obligation states and
the machine-readable `source-design.ndjson` authority are unchanged.

## Design queue

| Packet | Candidate Lean boundary | Prerequisite vocabulary | Required source gate | Discriminating check |
|---|---|---|---|---|
| `A1.1` | determinant-fixed global deformation functor and universal object | complete local Noetherian coefficient rings, strict equivalence, continuous matrix representations | exact Mazur/de Smit--Lenstra theorem and proof that each flat/ordinary condition is a closed representable subfunctor | exhibit a residual representation failing absolute irreducibility and confirm the universal-object theorem is unavailable |
| `A1.2` | local tangent and obstruction spaces for each selected deformation condition | continuous cohomology and local condition subspaces | exact dimension/Euler-characteristic locators for every local condition | change one local condition and show the dimension formula no longer typechecks or proves the old result |
| `A1.3` | Taylor--Wiles auxiliary-prime selector | dual Selmer group, Frobenius eigenvalue conditions, finite auxiliary sets | exact auxiliary-prime theorem, not merely Taylor--Wiles Theorems 1--2 | remove the distinct-eigenvalue condition and require the selector consumer to fail |
| `A1.4` | patched freeness/complete-intersection terminal | augmented Hecke rings, `O[Delta_Q]`, inverse systems, depth and numerical criterion | Taylor--Wiles Theorem 2 p. 557 plus the exact commutative-algebra bridge to Theorem 1 p. 556 | distinguish freeness of each auxiliary ring from the final `R = T` or complete-intersection conclusion |
| `A2.1` | forward cyclic base change of prime degree | global and local automorphic representations, restricted local components | freeze the actual section-2/section-11 Langlands result; reject “Theorem 11.2” | construct an invariant representation outside the verified image conditions and ensure descent is not inferred |
| `A2.2` | solvable base-change iteration and descent | towers of prime-degree cyclic extensions, twist ambiguity, invariant-image criterion | source every induction and descent step; prime-degree existence alone is insufficient | require recovery over the base field, not only existence after restriction |
| `A2.3` | Jacquet--Langlands transfer specialized to the selected definite quaternion algebra | local discrete-series predicate, conductor/level, coefficient embeddings, Hecke eigenvalues | a later proved source replacing the explicitly conjectural section-16 terminal and its formal sketch | alter one ramified local component and require level preservation to fail |
| `A3` | repository `J_v` bridge with `P_v <= J_v <= I_v` | exact definitions of wild inertia, inertia, tame character, and `J_v` | printed Serre locator plus a checked translation from its kernel/filtration to `J_v` | prove neither equality nor strictness without an additional hypothesis; test both boundary cases |
| `A4.1` | source-faithful incomplete Skolem datum and integral-point provider | schemes over a Dedekind base, local points and opens, finite surjective closed subschemes | Moret--Bailly Definition 1.2 p. 181 and Theorem 1.3 p. 182 | a complete Skolem datum must not satisfy the provider automatically |
| `A4.2` | FLT auxiliary-field assembly | total reality, Galois closure, even degree, unramifiedness, joint linear disjointness | separate primary lemmas for every field property and their simultaneous construction | satisfy each avoidance constraint separately but not jointly, and require the final constructor to fail |
| `A4.3` | auxiliary elliptic-curve realization | moduli point, coefficient transport, representation equivalences, good reduction and flatness | exact moduli specialization deriving the curve from the Skolem point | reject equality of representations when only dimensions or traces at a finite sample agree |
| `A5.1` | Brauer virtual-family construction | induction/restriction, virtual characters, solvable base change, coefficient fields | exact compatible-family specialization, not the misidentified 2009 Theorem A | a virtual difference must not be accepted as an effective family without positivity/integrality |
| `A5.2` | named-member recovery and scalar descent | stable lattices, semisimplified reduction, Brauer--Nesbitt, Chebotarev, scalar extension | exact theorem chain for equality from almost-all Frobenius data and descent to the named coefficient field | compare two arbitrary unrelated closure-valued representations and require the consumer to fail |
| `A6.1` | mod-3 finite-flat/discriminant classification core | finite-flat group schemes, ramification breaks, cut-out fields, root discriminants | inspected Fontaine/Poitou locators and a separate source for the `e_2 = 9` branch | keep the `e_2 = 9` case as an explicit uncovered constructor branch |
| `A6.2` | oriented invariant quotient | a Galois-stable line or quotient with a named trivial character | exact theorem selecting the orientation required by `mod_three` | swap subobject and quotient and require the downstream theorem to reject it |
| `A6.3` | 3-adic trace lift | compatible quotients or trace congruences modulo every `3^n`, completeness, Frobenius | a source connecting the residual classification to the characteristic-zero trace formula | mod-3 trace equality alone must not imply equality in the 3-adic coefficient ring |
| `B1` | four-field Frey `IsHardlyRamified` constructor | semistability, local reduction, unramifiedness, determinant, finite-flat torsion | one exact source locator per structure field | omit any one field and require construction of the final structure to fail |
| `B2.1` | source-faithful Weil pairing data | alternating/perfect pairing, roots of unity, base change, Galois equivariance | Tate's pairing formula plus a source/library construction of the pairing object | the zero biadditive map must fail perfectness or nondegeneracy |
| `B2.2` | Tate torsion local/global bridge | Tate parameterization over separable closure, local torsion action, specialization | exact uniformization and specialization sources | characteristic 2 and nonsplit multiplicative cases remain separate tests |
| `B3` | quaternion relative-index T3 proof | compact-open-to-order model, scalar quotient, norm-one units, finite square classes | keep Voight 2021 plus source the missing injection; do not substitute Voight 2017 Theorem 5.1 | a finite ideal-class set alone must not discharge the exact stabilizer-relative-index theorem |

## Primary-source supplement

The supplied Silverman and Diaz y Diaz PDFs change two source gates without promoting either
obligation.

| Packet | Newly verified source boundary | Lean construction aid | Residual gap |
|---|---|---|---|
| `A6.1` | Diaz y Diaz Table 1 gives the exact totally imaginary thresholds `n = 22 -> 10.25752840`, `n = 24 -> 10.66833176`, and `n = 4 -> 3.25456113`; Joshi Theorem 4.1 pp. 5--6 uses them in the restricted `F_3` nonirreducibility proof | first model the numerical thresholds and the totally-imaginary/even-degree adapters, then isolate Joshi's finite-group case split as a restricted nonirreducibility provider | the repository still needs a bridge from `IsHardlyRamified`, generalization beyond `F_3`, and the exact trivial-quotient orientation; `e_2 = 9` and the 3-adic trace lift remain separate no-results |
| `B2.2` | corrected Silverman V.5.3, printed pp. 442--444, equates base-field Tate form and split multiplicative reduction for a p-adic field with nonintegral `j` | restrict or bridge the local-form provider to the p-adic scope, instantiate the theorem, and combine it with the separately proved explicit Tate uniformization | the current generic local-field signature is broader; the theorem does not supply the analytic point map, finite-flat torsion object, or source-faithful Weil pairing |

## Admission rule

A future Lean task may select one row only when it records:

1. the exact source ID, source-byte digest, printed locator, and statement;
2. a field-by-field or hypothesis-by-hypothesis Lean translation;
3. the exact intended consumer and a negative/vacuity probe;
4. the trusted repository and Lean environment fingerprints;
5. targeted and full builds plus declaration-level axiom output; and
6. independent source-fidelity and Lean review.

The row is a planning aid until all six items exist. A successful interface probe is
not a proved provider, and a successful provider is not the closure of its downstream
component or the FLT programme.
