# FABLE 5 DIVERSITY REPAIR — P-adic-Hodge G1 crystalline infrastructure

## Verdict: `DESIGN-VIABLE`

All buildable claims below were compiled in disposable probes under `/tmp/fable5-g1-probes/`
(`P0`, `P0b`, `P0c`, `P1`, `P2`) with `lake env lean` against the exact pin
(`leanprover/lean4:v4.32.0-rc1`, mathlib `a3364faec42918fcd84a03a255b50570129f9ead`).
Every persisted-candidate declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`. No repository file, control row, graph row, or task
state was touched by this review. (Concurrent working-tree churn — commit `cc85ecc`, the untracked
`FLTMethodology/Probes/MLTCoefficientData.lean` — belongs to a parallel lane, not this task.)

## Context

Stage-9 (Opus) returned `DECOMPOSE-FIRST` with a bankable slice N0–N2; stage-11 (GPT-5.6 xhigh)
returned `REVISE-SUBSTANTIVE` with six required repairs. This is the independent Fable repair of
the bankable layer: exact hypotheses, exact instance assumptions, probed constructions, corrected
coefficient architecture, corrected role of Fontaine's `t`, and two new provider nodes. The full
G1 predicate (`IsCrystallineAt`), any comparison theorem, and the p-adic-Hodge obligation remain
out of scope and unpromoted.

---

## Repair 1 — `IsPlaceAbove`: exact non-vacuity hypotheses (PROBED, trio-clean)

Probe `P1`. The stage-9 signature `(ℓ : 𝓞 K) ∈ v.asIdeal` with bare `ℓ : ℕ` is vacuous at
`ℓ = 0`; the probe *machine-checks the counterexample*:

```lean
theorem unguarded_natCast_mem_of_zero (v : HeightOneSpectrum (𝓞 K)) :
    ((0 : ℕ) : 𝓞 K) ∈ v.asIdeal        -- vacuously true for EVERY place
```

Corrected definition (`[Fact ℓ.Prime]`, matching the Tier-1 `ℚ_[ℓ]` convention of
`FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`):

```lean
def IsPlaceAbove (ℓ : ℕ) [Fact ℓ.Prime] (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (ℓ : 𝓞 K) ∈ v.asIdeal
```

Non-vacuity is proved on all three axes, all compiled and trio-clean:

- `IsPlaceAbove.natCast_ne_zero` — the witness is a *nonzero* element of a *proper* ideal
  (`Nat.cast_ne_zero` + `hℓ.out.ne_zero`; `CharZero (𝓞 K)` synthesizes at the pin);
- `IsPlaceAbove.unique` — a place lies above at most one prime, via
  `Nat.isCoprime_iff_coprime`, `Nat.coprime_primes`, `IsCoprime.map (algebraMap ℤ (𝓞 K))`,
  and `v.isPrime.ne_top`;
- `exists_prime_natCast_mem` — every place lies above *some* prime (beyond what stage-11
  demanded), via `Ideal.absNorm_mem` / `Ideal.absNorm_eq_zero_iff`, primality of the comap
  `J = v.asIdeal.comap (algebraMap ℤ (𝓞 K))` (`Ideal.IsPrime.comap`), the PID generator
  (`Submodule.IsPrincipal.principal`, `Ideal.span_singleton_prime`), and
  `Int.prime_iff_natAbs_prime` + `Int.dvd_natAbs`.

So `IsPlaceAbove` with `[Fact ℓ.Prime]` carves out exactly one rational prime per place —
a genuine partition, not a tautology.

## Repair 2 — Scalar-compatible diagonal tensor action (PROBED, trio-clean)

Probe `P2`. Exact hypothesis block, with **both** `SMulCommClass` assumptions stage-11
demanded (they are precisely the `E`-linearity of the factor actions, consumed by
`DistribMulAction.toLinearEquiv E B g : B ≃ₗ[E] B`, which at the pin requires
`[Group Γ] [DistribMulAction Γ B] [SMulCommClass Γ E B]`):

```lean
variable (Γ : Type*) [Group Γ]
variable (E : Type*) [CommRing E]
variable (B : Type*) [CommRing B] [Algebra E B] [MulSemiringAction Γ B] [SMulCommClass Γ E B]
variable (V : Type*) [AddCommGroup V] [Module E V] [DistribMulAction Γ V] [SMulCommClass Γ E V]

noncomputable def diagTensorAut (g : Γ) : (B ⊗[E] V) ≃ₗ[E] (B ⊗[E] V) :=
  TensorProduct.congr (DistribMulAction.toLinearEquiv E B g)
    (DistribMulAction.toLinearEquiv E V g)

@[simp] theorem diagTensorAut_tmul :
    diagTensorAut Γ E B V g (b ⊗ₜ[E] x) = (g • b) ⊗ₜ[E] (g • x) := rfl

noncomputable def diagTensorRep : Γ →* ((B ⊗[E] V) ≃ₗ[E] (B ⊗[E] V))   -- map_one/map_mul proved
```

**Instance-diamond finding (new, sharper than stage-11):** probe `P0b` shows
`SMul Γ (B ⊗[E] V)` does **not** synthesize under this hypothesis order — mathlib's left-factor
instance needs `SMulCommClass E Γ B` and `SMulCommClass.symm` is only a *local* instance in
`LinearAlgebra/TensorProduct/Basic.lean` (line 338). The design must therefore (a) never
introduce a global `SMul Γ (B ⊗[E] V)` instance (a symmetric-`SMulCommClass` context would then
collide with `TensorProduct.leftHasSMul`, silently acting on the left factor only), and (b) never
write `g • x` on the tensor product — the Γ-action lives *only* in `diagTensorAut`/`diagTensorRep`.

## Repair 3 — Invariant submodule with explicit scalar closure (PROBED, trio-clean)

Probe `P0c` machine-confirms stage-11's claim in a stronger form:
`SMulCommClass Γ (FixedPoints.subring B Γ) (B ⊗[E] V)` is not merely unsynthesized — it is
**unstatable** (its `SMul Γ (B ⊗[E] V)` argument has no instance). Closure must be a hand proof.
Probe `P0` confirms the module scaffolding that *does* synthesize at the pin:
`Module B (B ⊗[E] V)`, `Module (FixedPoints.subring B Γ) (B ⊗[E] V)`, membership in
`FixedPoints.subring B Γ` defeq to `∀ g, g • b = b` (`hb g` typechecks), and subring smul
defeq to ambient smul (`rfl`).

The key semilinearity lemma and the construction (probe `P2`):

```lean
theorem diagTensorAut_smul_left (g : Γ) (b : B) (x : B ⊗[E] V) :
    diagTensorAut Γ E B V g (b • x) = (g • b) • diagTensorAut Γ E B V g x
  -- by TensorProduct.induction; tmul case: smul_tmul' + smul_mul' (MulSemiringAction)

noncomputable def periodSubmodule : Submodule (FixedPoints.subring B Γ) (B ⊗[E] V) where
  carrier := {x | ∀ g : Γ, diagTensorAut Γ E B V g x = x}
  zero_mem' g := map_zero _
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  smul_mem' := by            -- EXPLICIT closure: ⟨b, hb⟩ • x with hb : ∀ g, g • b = b
    rintro ⟨b, hb⟩ x hx g
    show diagTensorAut Γ E B V g (b • x) = b • x
    rw [diagTensorAut_smul_left, hb g, hx g]
```

Plus `mem_periodSubmodule` (`Iff.rfl`) and the sanity theorem
`periodSubmodule_eq_top` (trivial action ⇒ invariants are everything), all trio-clean.

## Repair 4 — Coefficient architecture: Option A, `E = ℚ_[ℓ]` exactly (PROBED)

Decision: **formalize `E = ℚ_[ℓ]` first; the finite-extension target is a separate deferred
node over `K₀ ⊗[ℚ_[ℓ]] E`.** Grounds: for ramified `E/ℚ_[ℓ]`, `E` does not embed in `B_cris`
(inside `B_dR` one has `B_cris ∩ K = K₀`), so `B_cris ⊗[E] V` is not even well-formed as a
balanced tensor, and `(B_cris ⊗[ℚ_[ℓ]] V)^Γ` is a `K₀ ⊗[ℚ_[ℓ]] E`-module of `K₀`-dimension up
to `[E:ℚ_[ℓ]] · dim_E V` — stage-9's generic-`E` `IsCrystallineRel` (fixed scalars read as `K₀`,
tensor over arbitrary `E`) conflates these and is wrong exactly as stage-11 said.

`periodSubmodule` stays `E`-generic (no dimension claim, hence safe); the *predicate* is pinned
to `ℚ_[ℓ]`, and the fixed scalars stay the abstract `Bᴳ`, never named `K₀` (probe `P2`):

```lean
def IsCrystallineRelQp
    (Γ : Type*) [Group Γ] (ℓ : ℕ) [Fact ℓ.Prime]
    (B : Type*) [CommRing B] [Algebra ℚ_[ℓ] B] [MulSemiringAction Γ B] [SMulCommClass Γ ℚ_[ℓ] B]
    (V : Type*) [AddCommGroup V] [Module ℚ_[ℓ] V] [Module.Finite ℚ_[ℓ] V]
    [DistribMulAction Γ V] [SMulCommClass Γ ℚ_[ℓ] V] : Prop :=
  Module.finrank (FixedPoints.subring B Γ) (periodSubmodule Γ ℚ_[ℓ] B V)
    = Module.finrank ℚ_[ℓ] V
```

Deferred node **N-E [P]**: finite coefficients — `D` as a `K₀ ⊗[ℚ_[ℓ]] E`-module, crystallinity
as freeness of rank `dim_E V` (equivalently `finrank_{K₀} D = [E:ℚ_[ℓ]] · dim_E V`). Not stated now.

## Repair 5 — New owner/provider nodes (dependency-closure completion)

- **N-Cp [P] (local `C_p` Galois-action bridge), d=7.** Correction to stage-9's closure: the
  field itself *exists at the pin* — `Mathlib/NumberTheory/Padics/Complex.lean` (`PadicAlgCl p :=
  AlgebraicClosure ℚ_[p]`, `PadicComplex p = ℂ_[p] := UniformSpace.Completion (PadicAlgCl p)`,
  `PadicComplexInt`, normed/valued/alg-closed instances; author de Frutos-Fernández). What is
  absent (grep: zero `MulSemiringAction`/`≃ₐ[` hits in that file) is the action: a continuous
  `MulSemiringAction (Γ ℚ_[ℓ]) ℂ_[ℓ]` extending the `AlgEquiv` action on `PadicAlgCl ℓ` by
  isometry (uniqueness of the spectral norm extension ⇒ each σ is norm-preserving ⇒
  `UniformSpace.Completion.map` extends it), together with the `Γ Kᵥ ↪ Γ ℚ_[ℓ]`-side indexing
  via `Field.absoluteGaloisGroup.map` (FLT `AbsoluteGaloisGroup.lean`) — the G5 bridge. Owner:
  FLT methodology, upstream-candidate to mathlib.
- **N-PD [P] (PD-envelope of an ideal), d=8.** Confirmed absent at the pin:
  `Mathlib/RingTheory/DividedPowers/` contains only `Basic, DPMorphism, Padic, RatAlgebra,
  SubDPIdeal`; no envelope, no universal property. Required by N3 (`A_cris` = p-completed PD
  envelope of `W(𝒪_{C^♭})` along `ker θ`). Owner: FLT methodology, tracking any upstream
  divided-power-envelope PR; adopt only on exact declaration match.

## Repair 6 — Role of Fontaine's `t`; `B_crisᴳ = K₀` stays a theorem

Corrected statement of the period-element facts (stage-9's "t = generator of ker θ" is wrong and
is retracted):

- **ξ, not t, generates `ker θ`**: `ξ = [p^♭] − p ∈ A_inf = W(𝒪_{C^♭})` generates
  `ker (fontaineTheta)`; this principality is exactly mathlib's open TODO 3 in
  `RingTheory/Perfectoid/BDeRham.lean` ("Show that ker θ is principal when the base ring is
  integral perfectoid") and is the input the PD-envelope node needs.
- **t = log [ε]** converges only in `A_cris` (not in `A_inf`), satisfies `θ t = 0` and
  `g • t = χ_cyc(g) • t`; it generates `Fil¹ B_dR⁺ = ker θ_{B_dR⁺}` as a `B_dR⁺`-ideal
  (a theorem *comparing* t to ξ up to unit, downstream of ξ-principality and the B_dR⁺-DVR
  TODO 2), and `B_cris = A_cris[1/t]` — inverting t already inverts p (`t^{p−1} ∈ p · A_cris`
  up to unit), so stage-9's `A_cris[1/p][1/t]` is redundant but not wrong.
- **`B_cris^{Γ} = K₀`** (`K₀ = FractionRing (WittVector ℓ k(v))`) is provider theorem **N7**,
  never a structure field or a parameter identification. Until N7 lands, every produced
  declaration speaks only of `FixedPoints.subring B Γ` — as `IsCrystallineRelQp` above does.

## Repair 7 — Production slice, order, residual, gates, stop-losses

**Smallest exact production slice** (all compiled in probes, mathlib-only imports, no FLT
dependency): one file `FLTMethodology/Probes/MLTPadicHodgePeriodFunctor.lean`, namespace
`FLTMethodology.Taylor2018`, registered in `FLTMethodology.lean`, containing exactly

1. `unguarded_natCast_mem_of_zero` (guard), `IsPlaceAbove`, `natCast_ne_zero`, `unique`,
   `exists_prime_natCast_mem`  — probe `P1`;
2. `diagTensorAut`, `diagTensorAut_tmul`, `diagTensorRep`, `diagTensorAut_smul_left` — probe `P2`;
3. `periodSubmodule`, `mem_periodSubmodule`, `periodSubmodule_eq_top` — probe `P2`;
4. `IsCrystallineRelQp` — probe `P2`.

**Dependency order** (revised graph):

```
slice (above)                                    LANDED-READY, trio-audited in probes
  → N-Cp  [P] continuous Γ-action on ℂ_[ℓ]       d=7   (field exists; action absent)
  → N-PD  [P] PD-envelope of an ideal            d=8   (absent at pin)
  → N3    [P] A_cris                             d=9   (needs N-Cp, N-PD, ξ-principality)
  → N4    [P] Frobenius φ on A_cris              d=8
  → N5a   [P] ξ generates ker θ                  d=7   (mathlib BDeRham TODO 3)
  → N5b   [P] t = log[ε] ∈ A_cris, χ-eigenvector; t ~ ξ in B_dR⁺   d=8
  → N6    [P] B_cris = A_cris[1/t], continuous Γ-action             d=8
  → N7    [P] B_cris^Γ = K₀ (theorem provider)   d=9
  → N-E   [P] finite coefficients over K₀ ⊗[ℚ_[ℓ]] E               d=7
  → N9    [I] assembly: IsCrystallineAt := IsCrystallineRelQp at B_cris   d=4  (BLOCKED until N3–N7)
```

**First residual Lean goal** (the next genuinely open item after the slice): the norm-equivariance
step of N-Cp — `∀ σ : PadicAlgCl ℓ ≃ₐ[ℚ_[ℓ]] PadicAlgCl ℓ, Isometry σ` from uniqueness of the
spectral-norm extension (`spectralNorm.normedField` is the pinned instance), then
`UniformSpace.Completion.mapRingHom`-style extension to a `MulSemiringAction (Γ ℚ_[ℓ]) ℂ_[ℓ]`
with `ContinuousSMul`.

**Axiom gates:** every persisted declaration must `#print axioms` to exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `knownin1980s`, no custom axiom;
kernel output authoritative; any deviation reverts the slice.

**Stop-losses:**
- If registering the slice file surfaces an instance clash with the concurrent
  `MLTCoefficientData` lane (it touches `FLTMethodology.lean` right now), rebase the
  registration, never force it; coordinate through the controller.
- Never introduce `SMul Γ (B ⊗[E] V)` (global or scoped-leaking) — diamond with
  `TensorProduct.leftHasSMul` under symmetric `SMulCommClass`; if a later node needs the action
  as an instance, use a type synonym.
- If any future node is tempted to define `K₀`-scalars on `periodSubmodule` before N7, stop:
  that is the stage-11 failure mode recurring.
- N3–N7 must not be estimated as one task; each is a separate provider with its own review.
  If mathlib lands `A_cris`/envelope upstream, adopt only on exact-declaration match at a new pin.
- Prohibited in this slice and until N3–N8: `IsCrystallineAt`, any comparison theorem, any
  promotion of `FLT-MLT-PADIC-HODGE`.

## Verification

- Re-run: `lake env lean /tmp/fable5-g1-probes/P{0,1,2}.lean` (exit 0; audits exactly the trio);
  `P0b.lean`/`P0c.lean` must keep failing synthesis (expected-failure guards).
- On execution approval: copy the P1+P2 payload into
  `FLTMethodology/Probes/MLTPadicHodgePeriodFunctor.lean`, register the import, targeted
  `lake build` of that module, `#print axioms` gate on all 12 declarations, then delete
  `/tmp/fable5-g1-probes/`.
