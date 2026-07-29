# Fable 5 executable review — PASS

Agent: `fable5-executable-reviewer`

Model: `claude-fable-5`

Elapsed: `279967 ms`

Candidate commit reviewed: `ee0f49e`

Session: `2f100c5c-6dbb-4929-9f08-424e1c30d1d9`

Terminology correction: the response uses “uninhabited” once. The authoritative classification is
**unwitnessed**: repository search found no witness, which is not a proof that the proposition is
uninhabited.

Whitespace-normalized response follows; wording is exact. The byte-exact transcript remains in the
session ledger named above.

PASS

`PASS` applies strictly to the deterministic rank-two Chebotarev adapter at candidate commit `ee0f49e` as kernel-clean and now independently executed and reviewed. It does not certify density, any T2 assumption, `FLT-CHEBOTAREV`, the compatible-family terminal, or FLT.

---

## 1. Commands and results

All commands executed in this session against `/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730`; tracked sources and control state untouched, only `.lake` build artifacts written.

| Command | Result |
|---|---|
| `git status --short` | exit 0, empty — clean tree (re-confirmed clean after all builds) |
| `git rev-parse HEAD` | `a1506e3cca091fe51b1807c02cc9b021b8d21e53` |
| `git merge-base --is-ancestor ee0f49e HEAD` | exit 0 — candidate is an ancestor |
| `git diff --check 8929b77…c606..ee0f49e` | exit 0, no findings (prior review's whitespace defects repaired) |
| `git diff --name-status ee0f49e..HEAD` | exactly 3 added files, all review prompts/transcripts under `methodology/review/flt-completion/chebotarev/` — the "later commits are prompts/transcripts only" condition holds |
| `lake env lean --stdin < FLT/GaloisRepresentation/CompatibleFamilyComparison.lean` | exit 0 |
| `lake env lean --stdin < FLTMethodology/Probes/ChebotarevRankTwo.lean` | exit 0; printed all seven axiom closures (below) |
| `lake env lean --stdin < FLT.lean` | exit 0 |
| `lake env lean --stdin < FLTMethodology.lean` | exit 0 |
| `lake build FLT.GaloisRepresentation.CompatibleFamilyComparison FLTMethodology.Probes.ChebotarevRankTwo` | exit 0 — "Build completed successfully (3629 jobs)" |
| `lake build FLT FLTMethodology` | exit 0 — "Build completed successfully (9045 jobs)"; only a pre-existing style warning in `FLTMethodology/Scaffold.lean:10`, outside the candidate range |

Both prior reviews (read first, verdicts not copied) were `REVISE` solely because their execution environments could not write build artifacts. My environment is writable: **both mandatory Lake gates and all four direct stdin elaborations independently succeeded here.** Per instruction, `-H` was not added; the controller's separate hash-checked builds stand as recorded.

## 2. Axiom table

The module contains exactly seven public theorems (plus five `def`s, none of which is an axiom or witness). The probe covers all seven. Independently, both in the targeted Lake build log and via direct stdin elaboration of the probe, each printed exactly:

| Theorem | Axiom closure |
|---|---|
| `charpoly_conjugate` | `[propext, Classical.choice, Quot.sound]` |
| `charpoly_eq_of_dense_of_finrank_eq_two` | `[propext, Classical.choice, Quot.sound]` |
| `nonempty_equiv_of_dense_charpoly_eq` | `[propext, Classical.choice, Quot.sound]` |
| `nonempty_equiv_of_dense_conjugacy_charpoly_eq` | `[propext, Classical.choice, Quot.sound]` |
| `charpoly_globalArithFrob` | `[propext, Classical.choice, Quot.sound]` |
| `nonempty_representationEquiv_of_charFrob_eq_of_density` | `[propext, Classical.choice, Quot.sound]` |
| `GaloisRepFamily.isCompatible_charFrob_eq` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no custom density axiom. A repo sweep found `RatArithmeticFrobeniusConjugacyDensity` / `FrobeniusConjugacyDensityAt` / `conjugacySaturation` only at their definition and explicit-hypothesis sites — no hidden witness, no instance. The repository's known upstream `axiom` declarations (Mazur, Odlyzko, `knownin1980s`, etc.) are demonstrably outside all seven closures.

## 3. Mathematical recheck (all seven mandated points)

1. **Conjugacy saturation / counterexample.** `conjugacySaturation elements = {g | ∃ i x, g = x·eᵢ·x⁻¹}` is the full union of conjugacy classes — the set Chebotarev actually makes dense. The chosen-representative counterexample is defeated correctly: in a finite discrete quotient (e.g. `S₃`) one representative per class is not dense even when the class union is everything. The adapter demands density only of the saturation and charpoly equality only at representatives, extended across each class by `charpoly_conjugate`, whose proof realizes `ρ(xgx⁻¹) = e.conj (ρ g)` with `e = ρ(x)` as a `LinearEquiv` and applies `LinearEquiv.charpoly_conj`. Sound.
2. **Continuity, rank two, `T2Space`.** `GaloisRep` is a continuous hom into `Module.End` under the module topology; trace continuity via `IsModuleTopology.continuous_of_linearMap`, determinant via `IsModuleTopology.continuous_det`, each composed with `rho.continuous`. Dense-to-everywhere extension is exactly `Continuous.ext_on hS` into the Hausdorff field — `T2Space k` is used precisely there and nowhere gratuitously (`charpoly_conjugate` and `charpoly_globalArithFrob` correctly `omit` it). Rank two is used exactly twice: extracting `det` as `coeff 0` (sign `(−1)² = +1` valid only at n = 2) and reconstructing `charpoly = X² − (tr)·X + C(det)` via `LinearMap.charpoly_of_finrank_eq_two`. No topology is placed on polynomials. `trace_eq_of_charpoly_eq` goes through `nextCoeff`, dimension-robust.
3. **Arithmetic normalization and `toLocal` bridge.** Mathlib's `IsArithFrobAt` requires `σ • x ≡ x^q (mod Q)` with `q` the residue cardinality — arithmetic Frobenius, matching Wiese's convention. `globalArithFrob v = Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) (Frob v)` uses the exact map underlying `GaloisRep.toLocal = ρ.map (algebraMap _ _)`, so `charpoly_globalArithFrob` is `rfl` — kernel-verified definitional agreement, not a coincidence of names.
4. **Finite exceptional sets.** `FrobeniusConjugacyDensityAt S` asserts density of the saturation of `frobeniusOutside S : {v // v ∉ S} → Γ K`; `RatArithmeticFrobeniusConjugacyDensity` quantifies over **every** `S : Finset (Ω ℚ)`. The comparison theorem consumes one `(S, hDensity)` pair with `hchar` outside that same `S`; no collapse to `S = ∅`, no hidden exceptional-set mismatch.
5. **Comparison conclusion.** Common coefficient field `k` for both sides, both semisimplicity hypotheses, both `finrank = 2` hypotheses, full characteristic-polynomial (not trace-only) equality, conclusion exactly `Nonempty (Representation.Equiv …)` via the reviewed Brauer–Nesbitt base `nonempty_representationEquiv_of_finrank_eq_two`. `isCompatible_charFrob_eq` is a faithful `simpa [GaloisRep.charFrob]` restatement of `isCompatible` — same `S`, `Pv`, unramifiedness, and `(p) ∉ v.asIdeal` disjointness; it introduces no second representation, semisimplicity, or coefficient transport.
6. **Sources.** The packet now correctly separates Gee Fact 2.27 (conjugacy-saturated density) from Remark 2.31 (Chebotarev + Brauer–Nesbitt comparison pattern) — the prior review's locator defect is repaired. Wiese Theorem 1.2.8 / Corollary 1.2.9 (finite Chebotarev; profinite Frobenius density) and lines 246, 266–270 (arithmetic Frobenius; conjugacy-class nature of the choice) match the encoded contract; Taylor's notes independently use the same pattern. This agrees with my own knowledge of these statements. The packet honestly records that an exact primary-source locator remains an open literature-assurance gap.
7. **Honest boundary.** File docstrings, source packet, evidence packet, `SOURCE-REGISTER.md`, and `proof-obligations.ndjson` are mutually consistent: density is an uninhabited proposition, no witness or T2 density assumption is asserted anywhere, and `FLT-CHEBOTAREV` remains `absent` / `revision-required`.

## 4. Findings, ordered by severity

1. **Low — stale graph vocabulary (known, honest).** `FLT-CHEBOTAREV` still names the proposed `FLT.CompatibleFamily.equal_of_charFrob_eq`, which does not exist. This correctly keeps the obligation open and blocks closure; it must eventually be split/rebound but does not affect this adapter approval.
2. **Low — pre-existing style warning.** `FLTMethodology/Scaffold.lean:10` module-docstring-placement lint warning in the umbrella build; the file is outside the candidate range and the build succeeds.
3. **Informational.** Both prior mechanical defects (candidate-range `diff --check`, probe docstring naming `RatArithmeticFrobeniusConjugacyDensity`) are confirmed repaired at `ee0f49e`. The evidence packet's build claims (3629 / 9045 jobs) exactly match my independent reproduction.

No mathematical, source, universe, topology, conjugacy, exceptional-set, coefficient, or import defect found.

## 5. Exact honest boundary

This `PASS` approves precisely: the deterministic adapter in `FLT/GaloisRepresentation/CompatibleFamilyComparison.lean` at `ee0f49e` is kernel-clean at exactly `[propext, Classical.choice, Quot.sound]`, independently rebuilt (targeted and umbrella Lake gates) and independently re-elaborated from exact sources, with sound mathematics and adequately aligned secondary sources.

It does **not** approve anything beyond that:

- `RatArithmeticFrobeniusConjugacyDensity` remains unwitnessed — density is consumed as an explicit hypothesis only;
- no Chebotarev T2 density assumption is authorized by this review;
- T3 requires a standard-trio proof of density;
- fixed-coefficient transport, determinant, semisimplicity, and consumer-specific compatible-family wiring remain open;
- the stale `equal_of_charFrob_eq` graph interface must be split/rebound before obligation closure;
- `FLT-CHEBOTAREV`, its downstream compatible-family terminal, and FLT remain open and unproved.

No tracked files, commits, or control state were changed; only `.lake` build artifacts were written.
