# Opus 4.8 primary design — tame-residue U3 roots-of-unity reduction

Reviewed commit: `e8b43d07f032852296a956282c268c0d34ac9da3`

Verdict: `READY-FOR-GPT-REVIEW`

Recommended bounded action: `BUILD-U3-SLICE`.

This was a read-only difficulty-8 pass. U1/U2 remained frozen. Temporary probes were created only
outside the repository and all proposed signatures were tested against Lean 4.32.0-rc1 and the
pinned Mathlib revision.

## Mathematical split

U4 will construct

```lean
tameResidueChar : localInertiaGroup v →* (IsLocalRing.ResidueField 𝒪ᵥ)ˣ
```

from the residue of a quotient `σx / x`, which is a `(q - 1)`-st root of unity, where
`q = Nat.card (IsLocalRing.ResidueField 𝒪ᵥ)`. The review separates three claims:

1. U3-A: reduction is injective on `(q - 1)`-st roots of unity in
   `IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)`;
2. U3-C: the `(q - 1)`-st roots in the enlarged residue field are identified with the units of the
   base residue field;
3. U5, not U3: every base residue unit has an integral root-of-unity lift. This is the
   Teichmüller/Henselian existence direction.

U3-A and U3-C are sufficient for the proposed U4 codomain and root-independence argument. U5 is a
later, stronger existence theorem and must not be used to justify U3 injectivity.

## Existing APIs verified

- `restrictRootsOfUnity`
- `restrictRootsOfUnity_coe_apply`
- `mem_rootsOfUnity` and `mem_rootsOfUnity'`
- `IsLocalRing.residue`
- `IsLocalRing.residue_eq_zero_iff`
- `IsLocalRing.residue_ne_zero_iff_isUnit`
- `IsLocalRing.ResidueField.map`
- `Fintype.card_units`
- `FiniteField.pow_card_sub_one_eq_one`
- `Nat.cast_card_eq_zero`
- `geom_sum_mul_add`
- `valuationRing_integralClosure`

The review found no existing equivalence

```lean
IsLocalRing.ResidueField (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)) ≃
  AlgebraicClosure (IsLocalRing.ResidueField 𝒪ᵥ)
```

and no local-reciprocity API. Neither may be assumed.

## Kernel-probed U3-A design

The reviewer proposed a general local-ring route:

```lean
theorem eq_one_of_pow_eq_one_of_residue_eq_one
    {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    {n : ℕ} (hn : IsUnit (n : 𝒪)) {u : 𝒪}
    (hpow : u ^ n = 1)
    (hres : IsLocalRing.residue 𝒪 u = 1) :
    u = 1

theorem rootsOfUnity_residue_injective
    {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    {n : ℕ} (hn : IsUnit (n : 𝒪)) :
    Function.Injective
      (restrictRootsOfUnity (IsLocalRing.residue 𝒪) n)
```

If `u` reduces to one, write `u = 1 + m` with `m` in the maximal ideal. The geometric-sum identity
shows that a sum reducing to `n` annihilates `m`. Since `n` is a unit, that sum is a unit, hence
`m = 0`. This requires no domain, Henselian, completeness, or reciprocity hypothesis.

For the actual place, the reviewer proved:

```lean
theorem isUnit_card_sub_one_ICv
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝒪 K)) :
    IsUnit
      ((Nat.card (IsLocalRing.ResidueField 𝒪ᵥ) - 1 : ℕ) :
        IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))

theorem tame_rootsOfUnity_residue_injective
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝒪 K)) :
    Function.Injective
      (restrictRootsOfUnity
        (IsLocalRing.residue (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
        (Nat.card (IsLocalRing.ResidueField 𝒪ᵥ) - 1))
```

The unit proof reduces `q - 1` to `-1` in the finite residue field and transports the resulting
unit along the algebra map into the integral closure.

The reviewer also proved the base finite-field identity:

```lean
theorem units_eq_rootsOfUnity_card_sub_one
    {F : Type*} [Field F] [Fintype F] :
    rootsOfUnity (Fintype.card F - 1) F = ⊤
```

Every probed declaration audited to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Remaining U3-C residual reported by Opus

Opus did not finish the enlarged-residue-field descent. Its first residual was to use

```lean
IsLocalRing.ResidueField.map
  (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
```

and prove that every `(q - 1)`-st root of unity in the target residue field lies in the range of
the induced base-residue-field map. It suggested finite-field splitting/counting, without assuming
an algebraic-closure identification or Henselian lifting.

The controller subsequently produced a separate kernel-clean cardinality proof for this residual;
that evidence is deliberately not attributed to the independent Opus design and is to be reviewed
at the next GPT gate.

## Stop-loss analysis

- If the residue characteristic divides the exponent, injectivity is false: nontrivial
  `p`-power roots may reduce to one.
- The residue map is defined on integral roots; nonintegral elements cannot be silently reduced.
- A non-Henselian local ring does not refute injectivity, but can refute the later lifting direction.
- No step may introduce reciprocity, alter `localTameAbelianInertiaGroup`, add a historical axiom,
  or claim U4–U6 complete.

## Bounded recommendation

Build only the reviewed U3 arithmetic slice and extend the existing tame-residue axiom probe. Keep
`FLT-TAME-RESIDUE` as a definition gap, leave the graph and consumers unchanged, and require the
mandatory GPT-5.6 xhigh review before persistence.

