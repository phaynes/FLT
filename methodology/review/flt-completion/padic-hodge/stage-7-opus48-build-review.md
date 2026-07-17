# Independent Opus 4.8 Build Review — p-adic-Hodge Tier-1 Weight Boundary

## Context

This is a read-only difficulty-10 build review of the persisted p-adic-Hodge Tier-1 boundary. The
task asks for a `PASS`/`REVISE` verdict where `lake build` and per-declaration `#print axioms` are the
final authority. **Plan mode is active and forbids running non-read-only tools** (`lake build` writes
`.lake/build` artifacts), so this document records the *complete read-only static verification* already
performed and specifies the single remaining kernel-authoritative gate to execute on approval.

Bounded unit reviewed (all present, committed at `dbc66d5`):
- `FLTMethodology/Probes/MLTPadicHodgeWeightData.lean`
- import at `FLTMethodology.lean:23`
- `methodology/review/flt-completion/padic-hodge/stage-4-opus48-synthesis.md`
- `methodology/review/flt-completion/padic-hodge/stage-5-gpt56xhigh-review.md`
- `methodology/review/flt-completion/padic-hodge/stage-6-pinned-library-gap-audit.md`

## Read-only findings against the ten required checks

1. **Global-embedding indexing — CONFIRMED.** `AbstractWeightData` (probe:19-22) is
   `(F →+* AlgebraicClosure ℚ_[ℓ]) → Multiset ℤ` with `[NumberField F]`. There is a single field `F`
   (the base), not a coefficient field; the domain is embeddings of `F`. Matches the repo idiom in
   `GaloisRepFamily.lean:38-64` and Taylor's normalization.
2. **`InFontaineLaffailleInterval` — CONFIRMED.** probe:39-43 binds one shared `a : ℤ` outside the
   `∀ τ n` quantifier; upper endpoint is `a + (ℓ:ℤ) - 2` (⇒ ℓ−1 consecutive integers). One global base,
   correct endpoint.
3. **Unramifiedness predicate — CONFIRMED exact.** probe:46-49 uses
   `Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ:ℤ)})`. Mathlib
   `RingTheory/Unramified/Locus.lean:98` defines `IsUnramifiedIn (A) [Algebra R A] (𝔭 : Ideal R)`; here
   `A = 𝓞 F`, `R = ℤ`, `𝔭 = (ℓ)` — the exact Mathlib predicate, correctly encoding "ℓ unramified in F".
4. **`GaloisRepDual` — CONFIRMED continuous contragredient, no missing topology hyp.** probe:71-88:
   `σ ↦ (ρ σ⁻¹).dualMap`, inverse on `σ` (forced by `dualMap` contravariance to satisfy `map_mul'`).
   The three `letI`s (`moduleTopology` on both `End`s + `toContinuousAdd`) reconstruct exactly the
   topology `GaloisRep` itself bakes in (`GaloisRep.lean:50-51`); this mirrors `GaloisRep.baseChange`
   (`:213-216`). Continuity = `endTranspose` (`continuous_of_linearMap`, Mathlib ModuleTopology:340) ∘
   `ρ` (`ρ.continuous_toFun`) ∘ `continuous_inv` (Γ K is a topological group). No `IsTopologicalRing A`
   is silently omitted — it is not needed; `Module.Finite`/`Module.Free` binders match `baseChange`.
5. **Two guards — CONFIRMED semantically.** `weightTwo_fits_iff_two_lt` (probe:91-111) proves
   `(∃ a, interval a {-1,0}) ↔ 2 < ℓ`; forward extracts `a ≤ -1` and `0 ≤ a+ℓ-2 ⇒ 3 ≤ ℓ`, backward uses
   `a=-1`. `repeatedWeightTwo_not_regular` (probe:114-122) proves `¬ IsRegularWeightData 2 (fun _=>{0,0})`
   via `Nodup` failure. Both instantiate `τ` through `Nonempty (F →+* AlgebraicClosure ℚ_[ℓ])`, which
   resolves via Mathlib `InfinitePlace/Embeddings.lean:46` (`[CharZero][IsAlgebraic ℚ][IsAlgClosed]`) —
   all satisfied. Threshold and repeated-weight rejection genuinely proved.
6. **Build + axiom audit — STATIC PRECONDITIONS MET; KERNEL EMISSION PENDING.** Probe already contains
   `#check` + `#print axioms` for all 7 defs + 2 guards (probe:124-142). Every upstream symbol resolves
   read-only. This is the one gate requiring execution (see Verification).
7. **No forbidden material — CONFIRMED.** `grep` shows no `sorry`, no `axiom` decl, no `IsCrystalline`,
   no HT extraction, no period-ring symbol. `HodgeTate`/`FontaineLaffaille` occur only as *this file's*
   own weight-matching / interval names, not extraction/crystalline predicates. No historical/provider
   assumption introduced.
8. **Pinned-library audit — REPRODUCED & correct.** Re-ran the stage-6 `rg`:
   `D_cris|IsCrystalline|HodgeTate|FontaineLaffaille|PeriodRing|B_cris` over `Mathlib` + `FLT` returns
   nothing for representation theory; the only `crystalline` hits are Berthelot–Ogus divided-power
   *crystalline cohomology*. The audit does not mistake cohomology for p-adic-Hodge rep theory.
9. **Obligation still a definition gap — CONFIRMED.** `proof-graph.ndjson:51` / `proof-obligations.ndjson`
   keep `FLT-MLT-PADIC-HODGE` at `current_state: definition-gap`, `kernel_probe_state:
   tier1-boundary-proof-green`, with G1/G2/G4/G5/G6/G7 explicitly named as open gaps. No promotion.
10. **Provider decomposition is proposal-only; graph unmutated — CONFIRMED.** `proof-graph.ndjson` and
    `proof-obligations.ndjson` are **not** in `git status`; no new obligation rows added. Stage-6's
    6-step split is prose labelled "only a proposed decomposition." Only telemetry control files show as
    touched (`flt-completion-execution.ndjson`, `source-design.ndjson`), and `git diff` shows no content
    delta — no graph mutation.

## Provisional verdict

On exhaustive read-only evidence: **PASS** on checks 1–5 and 7–10; check 6's static preconditions are
all met. The only item not yet witnessed by the Lean kernel *in this session* is the actual build +
axiom emission. First remaining mathematical provider: **G1 `GaloisRep.IsCrystallineAt` via a genuine
period-ring `D_cris` construction** (absent from the pin), followed by G2 HT-weight extraction and G4
the finite-flat→crystalline weight-two comparison (dominant risk). The full obligation must **not** be
promoted.

## Verification (kernel-authoritative gate — run on approval)

```bash
# targeted
lake build FLTMethodology.Probes.MLTPadicHodgeWeightData
# umbrella
lake build FLTMethodology
```
Then read the compiler's emitted `#print axioms` for each of the 9 declarations and require **exactly**
`[propext, Classical.choice, Quot.sound]` with **no** `sorryAx` — in particular for `GaloisRepDual`
(the sole elaboration risk: continuity of `dualMap` under the module topology). If the build is green
and every audit is the trio, finalize **PASS**; any `sorryAx`/extra axiom, missing `Nonempty`
instance, or build error → **REVISE** with the exact failing declaration. Lean's kernel output is
authoritative and overrides this static assessment.
