# S3 Reducibility Bridge — Primary Design (FLT-FONTAINE-ODLYZKO, difficulty 10)

**Verdict: `DESIGN-VIABLE`** (conditional on the two Lean probes below passing their
`#print axioms` gate — see §7, which I could **not** execute in plan mode and therefore do
**not** assert as proven).

---

## Context

The characteristic-three leaf `charP_three_of_zp3_algebra` is built and reviewed (stage-5 PASS,
bounded leaf only). The stage-3 review (REVISE) names the exact open residual node:

> "the exact arbitrary-`k` reducibility bridge: extract a stable rank-one submodule and quotient
> character from `¬ ρ.IsIrreducible`, with ranks, actions, and quotient orientation all explicitly
> typed. Fable's S3 uses undefined placeholders such as `stable`, `charOfSub`, and `~perm~`."
> (`stage-3-…-review.md:84–86`)

S3 is the arbitrary-finite-coefficient-field **linear-algebra** bridge only. It must derive a proper
`ρ`-stable rank-one submodule `W` and the canonical rank-one quotient `V ⧸ W`, correctly oriented,
**without** claiming the quotient character is trivial (that is later local/global input:
`ModThree.lean:32` proves triviality only from `IsHardlyRamified`, not from reducibility). This node
replaces Fable's placeholder S3 with exact, elaborating interfaces.

### What already exists (reused, not re-invented)

| Object | Location | Role |
|---|---|---|
| `GaloisRep K A M := Γ K →ₜ* Module.End A M` | `GaloisRep.lean:49` | the representation type; `ρ g : End`, `ρ g v` applies |
| `GaloisRep.toRepresentation ρ : Representation A (Γ K) M` | `GaloisRep.lean:399` | forgets topology; `= ρ.toMonoidHom` |
| `GaloisRep.IsIrreducible ρ := ρ.toRepresentation.IsIrreducible` | `GaloisRep.lean:404` | **exact def** we negate |
| `Representation.IsIrreducible σ := IsSimpleOrder (Subrepresentation σ)` | Mathlib `RepresentationTheory/Irreducible.lean:31` | the true unfolding |
| `Subrepresentation σ` (`toSubmodule` + `apply_mem_toSubmodule`), `BoundedOrder` `⊥=⟨⊥,_⟩ ⊤=⟨⊤,_⟩` | Mathlib `Subrepresentation.lean:31,92` | stable-submodule lattice |
| `Representation.subrepresentation W le_comap` / `Representation.quotient W le_comap` | Mathlib `Basic.lean:314 / 331` | sub- & quotient-rep from one `∀ g, W ≤ W.comap (σ g)` |
| `Submodule.finrank_quotient_add_finrank N : finrank (M⧸N) + finrank N = finrank M` | Mathlib `RankNullity.lean:246` | rank split (quotient summand **first**) |
| `Submodule.finrank_lt (h : s ≠ ⊤) : finrank s < finrank V` | Mathlib `FiniteDimensional/Lemmas.lean:46` | proper ⇒ strictly smaller |
| `Submodule.nontrivial_iff_ne_bot : Nontrivial p ↔ p ≠ ⊥` | Mathlib `Submodule/Lattice.lean:122` | nonzero ⇒ positive rank |
| `SemistableReducibleCharacterDichotomy` (posits line+quotient+exactness as **hypothesis data**) | `MazurSourceBoundary.lean:79` | precedent shape S3 must *derive*, not posit |

---

## 1. The smallest mathematically-true S3 output

Primary bankable object — a **theorem that derives** (not a structure that packages) the oriented split.
Universe-polymorphic; matches `ModThree.lean` hypotheses exactly (`Module.Finite`, `Module.Free`,
`Module.rank k V = 2`).

```lean
open Module (finrank)
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

theorem s3_reducibility_bridge
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hred : ¬ ρ.IsIrreducible) :
    ∃ (W : Submodule k V) (hW : ∀ g : Γ ℚ, W ≤ W.comap (ρ.toRepresentation g)),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧
      finrank k W = 1 ∧ finrank k (V ⧸ W) = 1 ∧
      Function.Surjective W.mkQ ∧
      (∀ (g : Γ ℚ) (v : V),
        W.mkQ (ρ g v) = Representation.quotient ρ.toRepresentation W hW g (W.mkQ v))
```

**Orientation (hostile check #1).** `W` is the rank-one **sub**; `V ⧸ W` is the rank-one **quotient**
reached by the canonical surjection `W.mkQ : V →ₗ[k] V ⧸ W`. This is the `→ 𝟙` position of the
consumer SES `0 → χ₃ → V → 𝟙 → 0` (`stage-3:41`; `ModThree.lean:27`). The stable interface is the
**quotient representation** `Representation.quotient ρ.toRepresentation W hW`, whose action is
`Submodule.mapQ W W (ρ.toRepresentation g) (hW g)`. The final `∀ g v` clause is exactly
`Submodule.mapQ_mkQ` composed with `ρ.toRepresentation g v = ρ g v`. **No triviality is asserted.**

Because `Representation.subrepresentation` and `Representation.quotient` consume the *same*
`hW : ∀ g, W ≤ W.comap (ρ.toRepresentation g)`, one stability proof yields both the rank-one
subrepresentation and the correctly-oriented rank-one quotient representation.

---

## 2. The multiplicative quotient character `χ : Γ ℚ →* k` — feasible, and canonical

**Determination: YES — a genuine multiplicative `χ : Γ ℚ →* k` can be built with no arbitrary basis
choice, and multiplicativity is *not* broken.** The reason is that basis-freedom lives in the
*endomorphism algebra of a line*, not in a chosen `V ⧸ W ≃ₗ[k] k`:

- `finrank k (V ⧸ W) = 1` ⇒ every `f : Module.End k (V ⧸ W)` equals `c • (1 : End)` for a **unique**
  `c` (unique because `V ⧸ W` is nontrivial). The scalar-extraction `End k (V⧸W) → k` is therefore a
  canonical ring map, *independent of any basis*.
- The quotient representation `Q := Representation.quotient ρ.toRepresentation W hW : Γ ℚ →* End k (V⧸W)`
  composed with this canonical extraction gives `χ`, and `map_one`/`map_mul` follow from scalar
  uniqueness. A concrete `V ⧸ W ≃ₗ[k] k` is **not** used — routing through it would introduce the
  basis choice the review's `~perm~` placeholder flagged. The character sidesteps it entirely because
  it acts by scalar multiplication directly on `V ⧸ W`.

Exact signature (slice 2), stated so the character acts by scalar on the quotient — no linear equiv:

```lean
theorem s3_quotient_character
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V) (hred : ¬ ρ.IsIrreducible) :
    ∃ (W : Submodule k V) (χ : Γ ℚ →* k),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ finrank k W = 1 ∧ finrank k (V ⧸ W) = 1 ∧
      Function.Surjective W.mkQ ∧
      (∀ (g : Γ ℚ) (v : V), W.mkQ (ρ g v) = χ g • W.mkQ v)
```

`χ : Γ ℚ →* k` uses the multiplicative monoid of `k`; values are automatically units (each `Q g` is
invertible since `Γ ℚ` is a group), so weakening to `→* kˣ` is available but unnecessary and `→* k`
matches the requested type. **`χ` is retained as a derived object; the primary stable interface remains
the quotient representation of §1.** We do **not** claim `χ = 1`.

---

## 3. Extraction from `¬ ρ.IsIrreducible` (exact current definition; `V = 0` branch excluded)

`ρ.IsIrreducible` unfolds to `IsSimpleOrder (Subrepresentation ρ.toRepresentation)`. `IsSimpleOrder`
= `Nontrivial ∧ (∀ a, a = ⊥ ∨ a = ⊤)`. Its negation has two branches; the `V = 0` / degenerate
branch sits in the `Nontrivial` clause and is killed **explicitly** by `Module.rank k V = 2`:

```lean
-- self-contained core, over an arbitrary Representation; no dependency on the Slop module
theorem exists_proper_invariant_submodule
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (σ : Representation k G V) [Nontrivial V] (hred : ¬ σ.IsIrreducible) :
    ∃ W : Submodule k V, (∀ g, W ≤ W.comap (σ g)) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  -- (a) Nontrivial V  ⇒  (⊥ : Subrepresentation σ) ≠ ⊤   [toSubmodule ⊥ = ⊥, ⊤ = ⊤ are rfl]
  have hbt : (⊥ : Subrepresentation σ) ≠ (⊤ : Subrepresentation σ) := fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Subrepresentation σ) := ⟨⊥, ⊤, hbt⟩
  -- (b) ¬ IsSimpleOrder, WITH Nontrivial in scope, ⇒ ¬ ∀ a, a = ⊥ ∨ a = ⊤
  have hnotall : ¬ ∀ a : Subrepresentation σ, a = ⊥ ∨ a = ⊤ :=
    fun h => hred { eq_bot_or_eq_top := h }
  push_neg at hnotall
  obtain ⟨a, hb, ht⟩ := hnotall
  exact ⟨a.toSubmodule, fun g v hv => a.apply_mem_toSubmodule g hv,
    fun h => hb (Subrepresentation.toSubmodule_injective (by simpa using h)),
    fun h => ht (Subrepresentation.toSubmodule_injective (by simpa using h))⟩
```

The `V = 0` branch is impossible because step (a) turns `Nontrivial V` into
`Nontrivial (Subrepresentation σ)`, so the *only* way `IsSimpleOrder` can fail is the
`eq_bot_or_eq_top` clause — yielding a genuine intermediate `a ≠ ⊥, ⊤`. In
`s3_reducibility_bridge`, `Nontrivial V` is obtained from `finrank k V = 2` (hence `≠ 0`), so the
degenerate branch is discharged, not assumed away.

**Distinction (hostile check).** `exists_proper_invariant_submodule` **derives** the submodule; it is
not a `structure` packaging hypotheses. This is the contrast the brief demands vs.
`SemistableReducibleCharacterDichotomy` (`MazurSourceBoundary.lean:79`), which *posits* line/quotient
data as fields. (An optional `structure S3Split` may wrap the §1 conclusion for downstream ergonomics,
but the bankable content is the theorem.)

---

## 4. Rank / quotient formulas under `Module.Finite`/`Module.Free` and general universes

```lean
theorem finrank_split_of_proper
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Submodule k V} (h2 : finrank k V = 2) (hb : W ≠ ⊥) (ht : W ≠ ⊤) :
    finrank k W = 1 ∧ finrank k (V ⧸ W) = 1 := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hb
  have hpos : 0 < finrank k W := finrank_pos                       -- Nontrivial + f.d.
  have hlt  : finrank k W < finrank k V := Submodule.finrank_lt ht  -- proper ⇒ strictly smaller
  have hW1  : finrank k W = 1 := by rw [h2] at hlt; omega
  have hadd := Submodule.finrank_quotient_add_finrank W            -- finrank(V⧸W) + finrank W = finrank V
  rw [h2, hW1] at hadd
  exact ⟨hW1, by omega⟩
```

- `Module.rank k V = 2 ⇒ finrank k V = 2`: with `Module.Finite k V`,
  `finrank k V = (Module.rank k V).toNat = (2 : Cardinal).toNat = 2` (`Module.finrank` is
  `(rank).toNat`; discharge with `Module.finrank_eq_rank`/`Cardinal.toNat_ofNat` + `hV`). `Nontrivial V`
  then follows from `finrank ≠ 0` (or directly from `rank ≠ 0`).
- `Module.Free k V` + `Module.Finite k V` ⇒ `FiniteDimensional k V` (instance). Over a field every
  submodule and quotient is automatically free/finite, so `finrank_pos`,
  `Submodule.finrank_quotient_add_finrank` (needs only `Module.Finite k V`), and `Submodule.finrank_lt`
  all apply with no extra freeness hypotheses on `W` or `V ⧸ W`.
- **Universes:** `k : Type u`, `V : Type v` independent; `GaloisRep`, `Representation`,
  `Subrepresentation`, `Representation.quotient`, and all finrank lemmas are universe-polymorphic. No
  `Type`-level pinning is introduced beyond `ModThree.lean`'s own `k : Type u`.

---

## 5. Dependency-ordered exact declarations

1. `exists_proper_invariant_submodule` (§3) — extraction; over generic `Representation k G V`, `[Group G]`.
2. `finrank_split_of_proper` (§4) — rank arithmetic; independent of (1).
3. `s3_reducibility_bridge` (§1) — GaloisRep wrapper: `finrank k V = 2` from `hV`; `Nontrivial V`;
   apply (1) to `ρ.toRepresentation`; apply (2); assemble with `W.mkQ_surjective` and
   `Submodule.mapQ_mkQ` (+ `ρ.toRepresentation g v = ρ g v`).
4. `endLine_scalar` (residual, §6) — `finrank k L = 1 → ∀ f : End k L, ∃ c, f = c • 1`.
5. `s3_quotient_character` (§2) — depends on 3 + 4; builds `χ` as `MonoidHom` via scalar uniqueness.

**Smallest safe production slice:** declarations **1–3** (`s3_reducibility_bridge` and its two lemmas).
This is fully library-routine, canonical, basis-free, and carries the entire oriented rank-one
sub / rank-one quotient + equivariance content the consumer needs first. Slice 2 (`χ`, decls 4–5) is a
separate bankable follow-up because it requires the one genuinely new piece of API (decl 4).

---

## 6. First residual Lean goal

After decls 1–3 close on library lemmas, the first non-routine goal is the line-scalar extraction that
powers `χ` (decl 4):

```lean
example {k L : Type*} [Field k] [AddCommGroup L] [Module k L] [Module.Finite k L] [Module.Free k L]
    (h1 : Module.finrank k L = 1) (f : Module.End k L) :
    ∃ c : k, f = c • (1 : Module.End k L) := by
  sorry   -- FIRST RESIDUAL GOAL
```

Proof route (bounded): `finrank_eq_one_iff'` gives a spanning `e ≠ 0`; write `f e = c • e`; extend to
all `w = a • e` by linearity. Uniqueness of `c` (from `L` nontrivial) then makes
`χ g := choose (endLine_scalar h1 (Q g))` a `MonoidHom` (`map_one`, `map_mul` by uniqueness). If Mathlib
already exposes `End k L ≃ₐ[k] k` / a "scalar of finrank-one endomorphism" lemma, decl 4 collapses to
that; the probe (§7) resolves which.

---

## 7. Probes and the axiom gate — NOT executed in plan mode

Plan mode forbids writing/running files, so **the two probes below were not run** and their axiom
closure is a **prediction, not a verified result** (per the brief: never treat a model assertion as a
proof). Execution is the first build step after approval.

- **Probe A** — decls 1–3 (slice 1) in a standalone file outside the repo, classic `import`
  (`FLT.Deformations.RepresentationTheory.GaloisRep`, `Mathlib`), closing with
  `#check @s3_reducibility_bridge` and `#print axioms s3_reducibility_bridge`.
- **Probe B** — decls 4–5 (slice 2), `#print axioms s3_quotient_character`.

**Required gate:** each `#print axioms` must print **exactly** `[propext, Classical.choice, Quot.sound]`.
Predicted to hold: the proofs use only `Submodule`/`Representation`/`finrank` API, `by_contra`/`push_neg`
(classical), quotient modules (`Quot.sound`), and `Classical.choose` for `χ`. No `sorryAx`, no
`native_decide`, and **no import of** `FLT.Assumptions.Mazur`, Odlyzko/Fontaine assumptions,
`knownin1980s`, N1 (`Fontaine_statement`), or N2 (`FlatLocalSplit_statement`). This must be **confirmed
by running the probe**, not assumed.

**Build command (post-approval):**
`lake env lean /path/to/tmp/S3Probe.lean` from the repo root (uses the existing `.lake` build; writes
only a scratch file outside the repo tree).

### Verification checklist (post-approval, in order)
1. Run Probe A; confirm it elaborates with no `sorry` and axioms `= [propext, Classical.choice, Quot.sound]`.
2. Resolve `ρ.toRepresentation g v = ρ g v` (expect `rfl`/simp) and the `Module.rank → finrank` cast; if
   either needs a bridging lemma, add it above decl 3.
3. Discharge the §6 residual; run Probe B; confirm identical axiom closure.
4. Only then port into the repo `module` system (mirroring `ModThree.lean`: `module`,
   `@[expose] public section`, `public import`) as the production slice.

---

## Hostile-check audit

| Check | Status |
|---|---|
| Do not reverse quotient orientation | `W` = rank-1 sub, `V⧸W` = rank-1 quotient via `mkQ` (the `→𝟙` position). ✔ |
| Do not infer trivial quotient from reducibility | No `χ = 1` / `π(ρ g v)=π v` claim; `χ` left general. ✔ |
| No undefined placeholders (`stable`, `charOfSub`, `~perm~`) | Stability = `∀ g, W ≤ W.comap (σ g)`; character = canonical scalar extraction; every symbol elaborates. ✔ |
| No `sorryAx`/`knownin1980s`/`Odlyzko_statement`/N1/N2 imports | None imported; gated by §7 axiom check. ✔ (pending run) |
| Don't weaken `k` to `ZMod 3` | `k : Type u` arbitrary `[Field k]`; no `ZMod 3` specialization. ✔ |
| Exclude spurious `V = 0` branch | `Nontrivial V` from `rank = 2` kills the `Nontrivial (Subrepresentation)` failure branch (§3). ✔ |
| Structure-packaging vs. derivation | `exists_proper_invariant_submodule`/`s3_reducibility_bridge` **derive**; contrasted with the *positing* `SemistableReducibleCharacterDichotomy`. ✔ |

---

## Verdict: `DESIGN-VIABLE`

The route is constructive, universe-polymorphic, arbitrary-`k`, correctly oriented, and axiom-clean by
construction, resting entirely on confirmed current Mathlib/FLT API. The only new mathematics is the
bounded §6 line-scalar lemma. Viability is **conditional** on the §7 probes reproducing exactly
`[propext, Classical.choice, Quot.sound]`, which must be executed (not assumed) as the first build step.
