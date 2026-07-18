# GPT-5.6 xhigh independent review — tame-residue U3

Act as an independent hostile mathematical and Lean reviewer at difficulty 8. Review the exact
commit supplied by the launch wrapper. Repository source, control artifacts, task state, review
packets, and git are read-only. Temporary Lean probes outside the repository are allowed and
required. Do not trust producer claims without reproducing them.

Review only U3. U1/U2 are frozen and independently sealed. U4 `tameResidueChar`, U5 Henselian
lifting, U6 the kernel theorem, source authorization, graph promotion, and all reciprocity work are
out of scope.

Read in full:

- `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`;
- `FLTMethodology/Probes/TameResidueBoundary.lean`;
- `methodology/review/flt-completion/class-field/stage-19-prompt-opus48-u3-primary-design.md`;
- `methodology/review/flt-completion/class-field/stage-19-opus48-u3-primary-design.md`;
- `methodology/review/flt-completion/class-field/stage-17-controller-u1-u2-bounded-build.md`;
- `methodology/review/flt-completion/class-field/stage-18-opus48-tame-u1-u2-build-review.md`;
- the exact `FLT-TAME-RESIDUE` obligation and its four outgoing edges.

Also inspect and independently reproduce, rather than merely accepting, the controller probe at:

```text
/private/tmp/RootsUnityReductionSpecializationProbe.lean
```

If that temporary file is absent or unreadable, reconstruct its signatures from this prompt and
continue; absence is not a content failure.

## Two independent proof routes to adjudicate

### Opus U3-A route

Opus proposed a general local-ring theorem using `geom_sum_mul_add`:

```lean
theorem eq_one_of_pow_eq_one_of_residue_eq_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {u : R}
    (hpow : u ^ n = 1)
    (hres : IsLocalRing.residue R u = 1) : u = 1

theorem rootsOfUnity_residue_injective
    {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Injective
      (restrictRootsOfUnity (IsLocalRing.residue R) n)
```

It separately proved the needed place-specific unit/coprimality fact and the base finite-field
identity. Verify the statement in rings with zero divisors and verify every use of local-ring unit
criteria. A standard-trio audit is mandatory.

### Controller U3-A/U3-C route

The controller independently used the domain property of the actual integral closure and
`sub_one_dvd_natCast_of_pow_eq_one` to prove:

```lean
noncomputable def rootsOfUnityResidue
    (R : Type*) [CommRing R] [IsLocalRing R] (n : ℕ) :
    rootsOfUnity n R →* rootsOfUnity n (IsLocalRing.ResidueField R) :=
  restrictRootsOfUnity (IsLocalRing.residue R) n

theorem rootsOfUnityResidue_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (n : ℕ) (hn : (n : IsLocalRing.ResidueField R) ≠ 0) :
    Function.Injective (rootsOfUnityResidue R n)
```

It then constructed, for any injective ring homomorphism from a finite field into a domain:

```lean
noncomputable def finiteFieldUnitsToRootsOfUnity
    (k L : Type*) [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) :
    kˣ →* rootsOfUnity (Nat.card k - 1) L

theorem finiteFieldUnitsToRootsOfUnity_bijective
    {k L : Type*} [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) (hf : Function.Injective f) :
    Function.Bijective (finiteFieldUnitsToRootsOfUnity k L f)

noncomputable def finiteFieldUnitsEquivRootsOfUnity
    (k L : Type*) [Field k] [Finite k] [CommRing L] [IsDomain L]
    (f : k →+* L) (hf : Function.Injective f) :
    kˣ ≃* rootsOfUnity (Nat.card k - 1) L
```

The bijection proof is by exact cardinality: `kˣ` has cardinality `q - 1`, its map is injective,
and any domain has at most `q - 1` roots of `X^(q-1)-1`. This is claimed to remove the Opus U3-C
residual without any algebraic-closure identification or Hensel theorem.

At the actual place, with

```lean
S := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
```

the controller instantiated `IsLocalRing`, `IsDomain`, and
`IsLocalHom (algebraMap 𝒪ᵥ S)`, proved

```lean
((Nat.card (IsLocalRing.ResidueField 𝒪ᵥ) - 1 : ℕ) :
  IsLocalRing.ResidueField S) ≠ 0
```

and defined the U3 map U4 would consume:

```lean
noncomputable def tameRootsReduction_at_place :
    rootsOfUnity (Nat.card (IsLocalRing.ResidueField 𝒪ᵥ) - 1) S
      →* (IsLocalRing.ResidueField 𝒪ᵥ)ˣ

theorem tameRootsReduction_at_place_injective :
    Function.Injective (tameRootsReduction_at_place v)
```

The claimed probe output for the place-specific exponent lemma, finite-field bijection, equivalence,
combined map, and injectivity is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Mandatory hostile checks

1. Reproduce both U3-A routes and decide which is the smallest stable public theorem. Confirm whether
   the Opus theorem is valid without `IsDomain`.
2. Reproduce the finite-cardinality U3-C bijection. Check the `NeZero (q - 1)` instance, all
   `Nat.card`/`Fintype.card` conversions, `card_rootsOfUnity`, the map's injectivity, and the exact
   direction of the resulting equivalence.
3. Confirm that
   `ResidueField.map (algebraMap 𝒪ᵥ S)` is a genuine injective field homomorphism and that
   all required `ValuationRing`, `IsLocalRing`, `IsDomain`, `Finite`, and `IsLocalHom` instances
   synthesize in production declaration order.
4. Confirm that the combined map really has codomain `(ResidueField 𝒪ᵥ)ˣ`, not merely the
   enlarged residue field, and that it is injective.
5. Check that the counting proof establishes only residue-field descent of roots. It must not be
   mislabeled as surjective lifting from the integral closure; that lifting remains U5.
6. Check `q = 2`, missing coprimality, residue characteristic dividing the exponent, a non-Henselian
   local ring, and nonintegral roots as stop-loss cases.
7. Recommend exact public names and placement. Compare:
   - a reusable module such as `FLT.Mathlib.RingTheory.RootsOfUnity.ResidueField` for the generic
     local-ring and finite-field lemmas; and
   - only place-specific map/wrapper declarations in
     `FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup`.
   Reject unnecessary coupling if the generic module compiles independently.
8. Confirm that no theorem needs reciprocity, the fixed field, an algebraic-closure residue-field
   equivalence, completeness, a historical axiom, or a source-contract change.
9. Compile every accepted signature and `#print axioms` every accepted theorem/definition. Any
   unexpected axiom or `sorryAx` is a substantive STOP.
10. Give the exact bounded build surface if the design passes. The component and obligation must
    remain open after U3 because U4–U6 are absent.

## Typed diversity rule

Return exactly one primary verdict:

- `PASS-BUILD-U3`;
- `REVISE`;
- `REFUTED`;
- `NO-RESULT`.

For `REVISE`, classify it exactly as either:

- `SUBSTANTIVE-MATHEMATICAL-OR-STATEMENT-LEVEL`, which triggers Fable because difficulty 8 is above
  the Opus comfort ceiling; or
- `MECHANICAL-OR-SCOPE-ONLY`, which skips Fable.

A timeout is `NO-RESULT`, never a negative mathematical verdict. A PASS authorizes only the bounded
U3 build and its audit probe. It does not authorize U4–U6, source/T2 promotion, a graph-state
promotion, reciprocity, or a historical assumption.

