# Stage 1 alternative design — Fable 5

## Model and transport evidence

- Agent: `fable5-designer-d10`
- Configured model: `claude-fable-5`
- Backend transport: `claude-code`
- Role: `primary`
- Difficulty: `10/10`
- Scheduled design budget: `3600 s`
- Exit code: `0`
- Actual invocation elapsed: `1440655 ms`
- Claude session: `5ef88135-eb06-4305-8965-c4991ab876d3`
- Token audit: `41` unique provider request IDs across the primary session and its subagents
- Input tokens: `48,683`
- Cache-creation input tokens: `325,538`
- Cache-read input tokens: `1,583,459`
- Output tokens: `102,320`
- Total tokens including cache traffic: `2,060,000`
- Output characters returned through bridge: `4655`
- Full design-report characters recovered from Claude plan artifact: `26252`
- Bridge topology: `single`
- Bridge total duration: `1440655 ms`
- Workspace: `/Volumes/second-store/devel/proof-forks/FLT`
- Session: fresh independent one-shot
- Prompt: `methodology/review/flt-completion/fontaine-odlyzko/stage-1-prompt-fable5.md`
- Repository mutation authority: read-only; no model repository edits permitted
- Claude plan source: `/Users/philiphaynes/.claude/plans/independent-stage-1-design-compressed-sphinx.md` (copied verbatim below)

## Bridge completion message

`ExitPlanMode` is not exposed in this non-interactive session, so I'm closing out by delivering the review directly; the full design document is at `~/.claude/plans/independent-stage-1-design-compressed-sphinx.md`. Condensed result:

# Verdict: `DECOMPOSE-FIRST`

The mathematics closes completely — **with no discriminant tables and no Dickson classification** — but the obligation is not one buildable unit: two new named T2 axioms are required and **zero are currently authorized** (`historical-assumptions.ndjson` holds only the `HIST-UNRESOLVED` guard, and the producer ladder demands a human gate for any T2 axiom), plus three infra subcomponents that each warrant their own stage-1.

## Exact boundary
Target is `GaloisRepresentation.IsHardlyRamified.mod_three` (`ModThree.lean:27`, sorried) — verbatim signature quoted in the design; it is currently **orphaned**: nothing on the `flt` spine consumes it (`Threeadic.lean` has the import commented out; `Proof.lean` bottoms out at `torsion_not_isIrreducible` and `knownin1980s`-Mazur). **Orientation ruling:** the Lean conclusion (trivial *quotient*) is correct; the blueprint prose ("extension of cyclotomic by trivial") is an erratum — the trivial-*sub* version is falsified by the peu-ramifiée Kummer-2 module (Frey 3-torsion shape), which is hardly ramified with H⁰ = 0.

## Complete case split
- **R (reducible):** JH-matching at 2 ⇒ both characters unramified at 2 ⇒ ramified only at 3, tame by order-coprimality ⇒ Minkowski (`abs_discr_ge'`, **not** the weak `abs_discr_ge`, whose 2.356 asymptote silently fails) + quadratic enumeration ⇒ {φ₁,φ₂} = {1,χ}. R-1 (quotient 1): done. R-2 (quotient χ): must *split* — needs axiom N2 (local flat splitting, Oort–Tate/connected–étale) + produced Kummer computation (2 is not a cube in ℚ₃: units cubes ≡ ±1 mod 9).
- **I (irreducible ⇒ False):** cut-out field K totally complex (det(conj) = −1). n ≥ 18: rd < 2^{2/3}·3^{3/2} = 8.2484 < 8.25 (integer certificate 2⁴·3⁹ = 314 928 < 33⁶/4⁶ ≈ 315 299.8) contradicts `Odlyzko_statement`, using axiom N1 (Fontaine 1985 Thm A: v₃(𝔡) < 3/2). n < 18, 3∤n: unramified at 2, tame at 3, |disc| ≤ 3^{n−1} < Minkowski for even n ≥ 4; n = 2 impossible. n < 18, 3|n: normal Sylow-3 ⇒ Kolchin stable line ⇒ reducible; else n = 12, n₃ = 4 ⇒ A₄, which has **no faithful 2-dim rep in char ≠ 2** (det-parity on V₄) — the incumbent's "A₄ degree-12 exceptional case needing tables" is vacuous.

## Axiom boundary (historical vs produced)
Three named axioms total: existing **N0** `Odlyzko_statement` (Poitou 1977 p.17 eq. 26); new **N1** Fontaine different bound (Invent. Math. 81 (1985), Thm A), typed against `HasFlatProlongationAt` (real Hopf types, `GaloisRep.lean:383`); new **N2** flat local splitting (Oort–Tate 1970 / Mazur 1977 §I — exact locator pinning is gate G4). **Rejected:** table axioms and a Dickson axiom (the repo already *proves* Dickson at `FLT/Slop/PGL2/.../DicksonClassification.lean:54`, grep-clean). Everything else is produced.

## Hostile findings (new vs the incumbent `stage-1-opus48-primary.md`)
1. **e₂ = 9 soundness hole:** I₂-image is only *elementary abelian* ⊆ (k,+) a priori; without a produced cyclicity lemma (unique cubic totally-tame extension of ℚ₂^{ur}, via unit-cube surjectivity + Hensel), rd ≤ 2^{8/9}·3^{3/2} ≈ 9.62 > 8.25 (even > 9.3) and the Odlyzko contradiction fails. Margin on the whole argument is 0.0016.
2. **Orientation cannot be decided by discriminants:** ℚ(ζ₃, 2^{1/3}) (|d| = 2⁴·3⁷, v₃(d)/n = 7/6 < 3/2) carries both a flat R-1 module and the would-be R-2 counterexample — so N1 can never discharge R-2; a module-level input (N2) is irreducible.
3. Coefficient-field: k = 𝔽_{3^r} general is genuinely required (family coefficients), nonsplit-Cartan images are unbounded, and no Frobenius-semilinear descent is needed anywhere in this route.

## Tranches and gates
**First buildable tranche** (ready now, zero new axioms): the pure-algebra pack S1–S6 — char-3 coefficient lemma, JH matching, Kolchin 2×2, A₄ non-embedding, abelian-irreducible ⇒ cyclic, and the two numeric certificates. **Stop-losses:** G1 axiom authorization (hard block), G2′ e₂-cyclicity, G3 infra probes (tame-different upper bound, `differentIdeal` localization), G4 source pinning for N1/N2. **Completion:** `mod_three` at frozen type with `#print axioms` exactly ⊆ {propext, Classical.choice, Quot.sound, N0, N1, N2}. DoR: **BLOCKED** for the component, READY for Tranche 1 — consistent with, but sharper than, the control plane's current state.

## Full alternative design report

# INDEPENDENT STAGE-1 DESIGN — FLT-FONTAINE-ODLYZKO (hostile review)

Repo: `/Volumes/second-store/devel/proof-forks/FLT`, branch `methodology/varro-proof-program-20260716`, start SHA `827eb96`.
Obligation: `FLT-FONTAINE-ODLYZKO` → `modThree_classification_core` → `FLT-MOD3` (`mod_three`). Target stage **T2**.
Reviewer stance: read-only, independent of `stage-1-opus48-primary.md` (verdict UNCERTAIN, DoR BLOCKED); disagreements listed in §12.

## VERDICT: `DECOMPOSE-FIRST`

The mathematics closes completely — **without discriminant tables and without Dickson** — but the obligation is
not one buildable unit: it requires **two new named T2 axioms** (currently zero are authorized in
`methodology/control/historical-assumptions.ndjson`; the producer ladder requires an explicit human gate for any
T2 axiomatisation), plus **three infrastructure subcomponents** (§6 S-blocks D, E, F) that each warrant their own
stage-1. One previously unreported soundness hole (§8, R-2: inertia-at-2 cyclicity) must be closed by any design,
mine included. Not `OBSTRUCTION`: the Lean statement of `mod_three` is true as stated (§2, §8) and every case is
eliminated by a sourced or producible step. Not `DESIGN-VIABLE`-as-one-tranche: axiom authorization and the
D/E/F infra are hard prerequisites.

---

## 1. Context

`GaloisRepresentation.IsHardlyRamified.mod_three` (`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27`,
body `sorry`) asserts every mod-3 hardly ramified rep has a Galois-stable **trivial quotient**. It is the
Fontaine-style replacement for Langlands–Tunnell in the planned proof (docstring of
`FLT/Assumptions/Odlyzko.lean`). Consumer status (verified by grep over the whole tree):

- **Orphaned from the live spine.** `FLT/Proof.lean` (`flt` ← B1←B2←B3←B4) bottoms out at
  `FreyCurve.torsion_not_isIrreducible` (sorry, `Frey.lean:58`) and `FreyPackage.mazur` (`knownin1980s`,
  `Mazur.lean:30`). No Lean declaration consumes `mod_three`; `Threeadic.lean:9` has the import
  commented out (`-- will be needed for proof`). Only consumers: `#check` probes
  (`FLTMethodology/Probes/ExistingContracts.lean:25`) and the methodology proof graph
  (`FLT-MOD3` "admitted", depends on `FLT-FONTAINE-ODLYZKO` "absent").
- **Intended consumer** is `three_adic` (`Threeadic.lean:31`, trace Frob_p = 1+p for p ≥ 5), fed by the
  compatible family (`Family.lean:37 mem_isCompatible`), whose coefficient ring is the integers of a **finite
  extension of ℚ₃** — so the residue field `k` is a general `𝔽_{3^r}`, **not** `ZMod 3`. The general-`k`
  statement is genuinely required; any design using `|GL₂(𝔽₃)| = 48`-specific facts is wrong (§8 R-4).
- `Odlyzko_statement` (`FLT/Assumptions/Odlyzko.lean:58`) is likewise declared but consumed by nothing.

## 2. Exact theorem boundary

Verbatim target (the only signature to be proved; do not restate it):

```lean
theorem mod_three {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v
```

Hypothesis type `IsHardlyRamified` (`Defs.lean:96`, proved structure): `det` = 3-adic cyclotomic character via
`algebraMap ℤ_[3] k`; `isUnramified` outside {2,3}; `isFlat` at 3 (`GaloisRep.IsFlatAt`, Hopf-algebra
prolongation, `GaloisRep.lean:391`); `isTameAtTwo` = a surjection `π₂ : V →ₗ[k] k` intertwining with a rank-1
`δ : GaloisRep ℚ_[2] k k` that is unramified (inertia ≤ ker) with `δ² = 1`.

**Orientation ruling (settles the incumbent's G2 gate).** The Lean conclusion is *trivial quotient*. The
blueprint prose (`ch03freyreduction.tex`, label `hardly_ramified_mod3_reducible`) says "extension of the
cyclotomic character by the trivial representation" — under the standard convention (ext of A by B: 0→B→V→A→0)
that claims a trivial **sub**, which is **false**: the peu-ramifiée Kummer-class-2 module (nonsplit
0→χ→V→𝟙→0; det = χ ✓, ramified only at {2,3} ✓, flat at 3 since v₃(2)=0 [Serre, Duke 54 (1987), §2.4 + Prop.
in §2.8: flat ⟺ peu ramifiée] ✓, at 2 the χ-line is G₂-stable with trivial quotient δ=1 ✓) is hardly ramified
and has H⁰(V) = 0 (connecting map sends 1 to the nonzero class), hence **no trivial sub**. It *does* have a
trivial quotient — this is the 3-torsion shape of a Tate/Frey curve. So: Lean statement correct, blueprint
prose is an erratum (or uses the opposite convention); the trivial-QUOTIENT form is the strongest true one.
File an erratum note; do not change the Lean statement.

## 3. Complete finite case split

Let ρ be hardly ramified, k finite of char 3 (char forced: ker(ℤ_[3] → k) is a nonzero prime of the DVR ℤ_[3],
hence (3) — S1). Write χ for the mod-3 cyclotomic character (order 2, values ±1 ≠ each other in char 3,
surjective onto {±1} since [ℚ(ζ₃):ℚ] = 2), G = Im ρ, and (in case I) K = fixed field of ker ρ, so
Gal(K/ℚ) ≅ G, n := [K:ℚ] = |G|.

**Universal local lemma (L2).** From `isTameAtTwo` + det = χ (χ unramified at 2): both Jordan–Hölder characters
of V|_{G₂} are {δ, χδ⁻¹}, unramified at 2; hence I₂ acts by upper-triangular unipotents, i.e. the I₂-image is
an elementary abelian 3-group inside (k,+). With cyclicity (L2′, see §8 R-2) the I₂-image has order e₂ ∈ {1,3};
in particular tame at 2 (e₂ odd).

**Case R — reducible** (∃ stable line L, characters φ₁ = sub, φ₂ = quotient, φ₁φ₂ = χ):
- R-a (JH matching, S3): comparing the global filtration with the `isTameAtTwo` local filtration at 2
  (elementary 2-dim linear algebra: either the lines agree or the sub injects into the local quotient),
  {φ₁|₂, φ₂|₂} = {δ, χδ⁻¹} ⇒ **both φᵢ unramified at 2**.
- R-b (character classification): φᵢ: Γℚ → kˣ continuous, image order divides |kˣ| = 3^r − 1 (prime to 3),
  unramified outside 3. Its fixed field K_φ is cyclic of degree m prime to 3, ramified only at 3, and tame
  there *by order coprimality alone* (e | m). Tame different (S10) gives v₃(disc K_φ) ≤ m − m/e ≤ m − 1, so
  |disc| ≤ 3^{m−1}. Minkowski domination (S6b: 3^{m−1}·(4/π)^m·(m!)² < m^{2m} for m ≥ 4, any signature,
  via Mathlib `abs_discr_ge'`) kills m ≥ 4. m = 3 impossible (3 ∤ order). m = 2: quadratic field ramified only
  at 3 ⇒ ℚ(√−3) (disc enumeration; ℚ(√3) has disc 12, ramified at 2) ⇒ φ = χ. m = 1 ⇒ φ = 1.
  So **{φ₁, φ₂} ⊆ {1, χ}**, and φ₁φ₂ = χ with χ ≠ any square (order 2, nontrivial) forces {φ₁, φ₂} = {1, χ}.
- R-1 (φ₂ = 1): the quotient V/L is trivial — **done** (this branch includes the Frey-type nonsplit modules;
  no splitting is needed or true here).
- R-2 (φ₁ = 1, φ₂ = χ): must show the extension **splits** (a nonsplit such V has only one stable line, the
  trivial sub, whose quotient is χ ≠ 1 — no dodge exists). Two inputs:
  * **N2 (historical axiom)**: a flat G_{ℚ₃}-rep killed by 3 with trivial sub and cyclotomic quotient splits
    *locally at 3*. (Group-scheme content: Ext¹ over ℤ₃ of a μ₃-type by an étale type vanishes, via the
    connected–étale sequence + Oort–Tate; the connected–étale splitting is canonical, hence k-equivariant —
    no Raynaud 𝔽-vector-space-scheme input needed.)
  * **Produced Kummer computation (E)**: Ext(χ,𝟙) ≅ H¹(ℚ, μ₃ ⊗ k) ≅ (ℚˣ/(ℚˣ)³) ⊗ k (Kummer/Hilbert 90);
    unramified outside {2,3} restricts classes to span_k{[2],[3]}; the restriction to ℚ₃ is injective on this
    span ([3] has valuation 1 ≢ 0 (3); [2] is a unit and **2 is not a cube in ℚ₃** — unit cubes are ≡ ±1 mod 9,
    2 ≢ ±1 (9); triangular independence). Locally split (N2) ⇒ class 0 ⇒ **split** ⇒ project to the trivial
    factor. Done.

**Case I — irreducible ⇒ False.** Setup S7/S8: ker ρ is open (discrete k, finite GL) ⇒ K number field, Galois,
Gal ≅ G. S9: K is **totally complex**: every complex conjugation c has det ρ(c) = χ(c) = −1 ≠ 1 (c inverts ζ₃;
−1 ≠ 1 in char 3) ⇒ c ∉ ker ρ ⇒ no real place. Also det surjective onto {±1} ⇒ 2 | n.
- **I-1, n ≥ 18**: root-discriminant squeeze.
  At 2: tame, e₂ ∈ {1,3} (L2 + L2′) ⇒ v₂(disc) ≤ n(1 − 1/e₂) ≤ 2n/3.
  At 3: **N1 (Fontaine axiom)**: flat killed by 3 ⇒ local different exponent v₃(𝔡_w) < 3/2 (normalized), so
  v₃(disc) < 3n/2 (integer form 2·v₃(disc) ≤ 3n − 1).
  Elsewhere: unramified ⇒ no contribution.
  So |disc K| < (2^{2/3}·3^{3/2})^n and 2^{2/3}·3^{3/2} < 8.25 (integer certificate: 2⁴·3⁹ = 314 928 <
  33⁶/4⁶ = 1 291 467 969/4096 ≈ 315 299.8 — margin ≈ 0.0016 on the base). Contradicts
  `Odlyzko_statement` (needs `IsTotallyComplex K` ✓ and n ≥ 18 ✓).
- **I-2, n < 18, 3 ∤ n**: I₂-image is a 3-group of prime-to-3 order ⇒ trivial ⇒ unramified at 2; ramified only
  at 3 and tame by coprimality (e | n) ⇒ |disc| ≤ 3^{n(1−1/e)} ≤ 3^{n−1}. n even (det), n = 2 impossible
  (an order-2 image is ±scalar or a split involution, both reducible). For n ∈ {4, …, 16} even:
  Minkowski domination S6b (n ≥ 4) contradicts |disc| ≤ 3^{n−1} (n = 4 check: 27 < 43.06). No group
  classification, no tables.
- **I-3, n < 18, 3 | n**: let P be a Sylow 3-subgroup (unipotent, Kolchin 2×2).
  * P ⊴ G: the unique P-fixed line is G-stable ⇒ reducible, contradiction (S4).
  * P not normal: n₃ ≡ 1 (3), n₃ ≥ 4, n₃ | n/|P| ⇒ |P| = 3, n = 12, and the only order-12 group with n₃ = 4
    is A₄. **A₄ has no faithful 2-dim rep in char ≠ 2** (S5): the three involutions of V₄ would be conjugate
    under the C₃ (so none is −I, hence each ~ diag(1,−1), det = −1), but det(ab) = det(a)det(b) = 1.
    Contradiction. (Groups with *projective* image A₄/S₄/A₅ have |G| ≥ 24/48/120 and fall into I-1.)

Cases R-1, R-2, I-1, I-2, I-3 are exhaustive: reducible/irreducible; in R, {φ₁,φ₂} = {1,χ} leaves exactly the
two orientations; in I, trichotomy on n and 3 | n. ∎

## 4. Source locator for each nontrivial implication

| Step | Statement | Source (exact) | Status |
|---|---|---|---|
| N0 | rd ≥ 8.25, totally complex, n ≥ 18 | Poitou, *Sur les petits discriminants*, Sém. DPP 18 (1976/77), Exp. 6, eq. (26) & table p. 17 (SRC-007; numdam link in `Odlyzko.lean`) | existing axiom |
| N1 | flat killed by 3 ⇒ v₃(𝔡) < 1 + 1/(p−1) = 3/2 | Fontaine, *Il n'y a pas de variété abélienne sur ℤ*, Invent. Math. 81 (1985), Théorème A (bound e(n + 1/(p−1)) on ramification; different-exponent corollary §2); cf. blueprint ch03 closing remark | **new axiom, unauthorized** |
| N2 | flat ext of μ₃-type by étale over ℤ₃ splits | Oort–Tate, *Group schemes of prime order*, Ann. Sci. ÉNS 3 (1970) (order-3 classification) + connected–étale sequence (SGA 3; Tate's *Finite flat group schemes* exposition). Same Ext-vanishing used by Mazur, Publ. IHÉS 47 (1977), §I; **exact numbered statement must be pinned before the axiom lands (gate G4)** | **new axiom, unauthorized** |
| flat ⟺ peu ramifiée (counterexample only, not on proof path) | Serre, Duke Math. J. 54 (1987), §2.4, 2.8 (SRC-005) | cited, not formalized |
| R-a JH matching | 2-dim linear algebra | none needed (produced) | produced |
| R-b quadratic enum | disc(ℚ(√±3)) = −3 / 12 | standard; Mathlib cyclotomic disc for ζ₃ | produced |
| Minkowski | |disc| lower bound | Mathlib `NumberField.abs_discr_ge'` (`Discriminant/Basic.lean:209`) — **in library, no axiom** | library |
| Tame different = e−1 | upper bound | classical (Serre, *Corps Locaux*, III §6 Prop. 13); Lean route via monogenic x^e − π + `aeval_derivative_mem_differentIdeal` | produced (S10) |
| L2′ cubic tame cyclicity at 2 | exponent-3 quotient of I₂ is cyclic | classical (tame inertia procyclic, Iwasawa); producible concretely: every unit of ℚ₂^{ur} is a cube (residue field 𝔽̄₂ cube-surjective + Hensel, 3 ∈ ℤ₂ˣ) ⇒ unique cubic totally-tame ext | produced (S11) — see §8 R-2 |
| Kummer H¹(ℚ,μ₃) ≅ ℚˣ/(ℚˣ)³ | Hilbert 90 | Mathlib Hilbert 90 / `FieldTheory.KummerExtension`; continuous-cocycle bridge produced | produced (E) |
| Fontaine strategy overall | mod-3 route | blueprint `ch03freyreduction.tex` (SRC-003); `Odlyzko.lean` docstring | design source |

## 5. Historical vs produced

**Historical (named T2 axioms — exactly three, two new):**
- `Odlyzko_statement` (N0) — exists, unchanged.
- `Fontaine_statement` (N1) — new. Local different bound for flat prolongations killed by 3.
- `FlatLocalSplit_statement` (N2) — new. Local splitting, trivial-sub/cyclotomic-quotient orientation.

**Explicitly rejected axiom candidates** (incumbent design proposed them):
- Small-degree totally-complex discriminant minima (incumbent "N2"/tables) — *not needed* (I-2/I-3 close via
  Mathlib Minkowski + group theory), and the task brief forbids classification-from-tables.
- Dickson PGL₂ classification (incumbent "N3") — *not needed* (no projective-image analysis anywhere above);
  moreover the repo already holds a grep-clean proved classification
  (`FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean:54`, `FLT/KnownIn1980s/PGL2/Defs.lean:32/42` +
  `Proofs.lean`) — if ever wanted, it is library, not axiom (run `#print axioms` before relying).
- Any global "no nonsplit hardly-ramified extension" axiom — rejected as axiomatizing the theorem itself
  (violates the design contract's stop-loss).

**Produced (kernel-clean):** everything else — S1–S14 of §6, including both discriminant-assembly bridges,
the Kummer bridge, tame cyclicity at 2, and the final assembly.

## 6. Proposed Lean signatures, in build order

Names indicative; module `FLT.GaloisRepresentation.HardlyRamified.ModThreeCore` plus infra modules.

**Tranche 1 — pure algebra (no new axioms, no Galois infra):**
```lean
-- S1
theorem charP_three_of_zp3_algebra (k : Type*) [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3
-- S3 (JH matching, stated for 2-dim V over field k with two filtrations)
theorem jh_chars_of_two_filtrations {k V} [Field k] ... (hV : Module.rank k V = 2)
    (L L' : Submodule k V) (hL hL' : stable, rank 1) :
    (charOfSub L, charOfQuot L) ~perm~ (charOfSub L', charOfQuot L')
-- S4 (Kolchin 2×2 + normal Sylow ⇒ stable line)
theorem exists_stable_line_of_normal_unipotent {k V} [Field k] [CharP k 3] ...
-- S5
theorem A4_no_faithful_two_dim {k V} [Field k] (h2 : (2:k) ≠ 0) (hV : rank = 2)
    (f : alternatingGroup (Fin 4) →* (V ≃ₗ[k] V)) : ¬ Function.Injective f
-- S6a (numeric certificate)
theorem rd_lt : (2:ℝ)^((2:ℝ)/3) * 3^((3:ℝ)/2) < 8.25   -- via 2^4*3^9 < 33^6/4^6
-- S6b (Minkowski domination, consumes NumberField.abs_discr_ge')
theorem minkowski_dominates_tame (n : ℕ) (hn : 4 ≤ n) :
    (3:ℝ)^(n-1) * (4/π)^n * (n.factorial)^2 < n^(2*n)
-- S2 (abelian irreducible ⇒ cyclic; order-2 image reducible)
```

**Tranche 2 — axiom statements (BLOCKED on operator authorization, gate G1):**
```lean
-- N1: place v₃ := (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by norm_num : (3:ℕ).Prime))
axiom Fontaine_statement {k V ...} [Field k] [Finite k] ... (ρ : GaloisRep ℚ k V)
    (h3 : CharP k 3) (hflat : ρ.HasFlatProlongationAt v₃) :
    -- L := IntermediateField.fixedField (ρ.toLocal v₃).ker, finite over the completion;
    2 * differentExponent L ≤ 3 * ramificationIdx L - 1
axiom FlatLocalSplit_statement ... (hflat : ρ.HasFlatProlongationAt v₃)
    (L : Submodule k V) (hsub : trivial G₃-action on L, rank 1)
    (hquot : G₃ acts on V ⧸ L via cyclotomic) :
    ∃ (s : V ⧸ L →ₗ[k] V), section, G₃-equivariant
```
Both are typed against `HasFlatProlongationAt` (`GaloisRep.lean:383`) — real Hopf-algebra content, no phantom
"group scheme" type. A mini-lemma discharges `IsFlatAt ⇒ HasFlatProlongationAt` for discrete field
coefficients (open ideal ⊥, `baseChange` by k/⊥ ≅ ρ).

**Tranche 3 — infra subcomponents (each its own stage-1; DECOMPOSE-FIRST core):**
```lean
-- D: cut-out field + discriminant assembly
def GaloisRep.cutOutField (ρ) (hopen : IsOpen (ρ.ker : Set (Γ ℚ))) : IntermediateField ℚ (ℚᵃˡᵍ)
instance : NumberField (cutOutField ...) ; instance : IsGalois ℚ (cutOutField ...)
theorem card_gal_cutOutField : Nat.card (Gal) = Nat.card (Im ρ)
theorem isTotallyComplex_cutOutField (hdet : ∀ c conj, ρ.det c = -1) : IsTotallyComplex K
theorem discr_le_of_local_data :  -- |disc| from per-prime different exponents
    (unram outside {2,3}) → (v₂ data) → (v₃ data) → |(discr K : ℝ)| < (2^(2/3)*3^(3/2))^n
-- S10 (inside D): tame different exponent
theorem differentIdeal_exponent_of_tame ... : d_w = e_w - 1
-- S11 (inside D): L2′ tame cubic cyclicity at 2
theorem cyclic_of_exponent_three_inertia_at_two ...
-- E: Kummer bridge
theorem exists_kummer_class ... :  -- from R-2 data, m ∈ span{2,3} ⊆ ℚˣ/(ℚˣ)³ ⊗ k
theorem two_not_cube_Q3 : ¬ ∃ x : ℚ_[3], x^3 = 2
theorem restriction_injective_on_span : ...
-- F: inertia bridge (FLT localInertiaGroup ↔ Ideal.ramificationIdx / differentIdeal of K)
```

**Tranche 4 — case theorems and join:**
```lean
theorem reducible_case ...      -- R-a + R-b + R-1 + R-2 (uses N2, E)
theorem irreducible_case ...    -- I-1 + I-2 + I-3 (uses N0, N1, D, F, S4–S6, S11) : False
theorem modThree_classification_core ... -- assembles the two
theorem mod_three ... := modThree_classification_core ...   -- one-line join, exact frozen type
```

## 7. Library matches (verified paths, pinned Mathlib `a3364fa…` via `.lake/packages/mathlib`)

- `NumberField.abs_discr_ge'` / `abs_discr_ge_of_isTotallyComplex` / `abs_discr_rpow_ge_of_isTotallyComplex` /
  `abs_discr_gt_two` — `NumberTheory/NumberField/Discriminant/Basic.lean:209/224/230/274`. Note: the weak
  `abs_discr_ge` ((4/9)(3π/4)^n, asymptote 2.356) is **insufficient** for I-2/R-b; use `abs_discr_ge'`.
- `NumberField.discr` defs + `absNorm_differentIdeal` (`Discriminant/Different.lean:43`),
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` (:89), `not_dvd_differentIdeal_iff`,
  `pow_sub_one_dvd_differentIdeal` (:739, lower bound only — upper is S10).
- `differentIdeal` + tower lemmas — `RingTheory/DedekindDomain/Different.lean:475`.
- `cyclotomicCharacter` + `.spec/.toZModPow/.continuous` — `NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
  (no surjectivity/kernel lemmas — produce via [ℚ(ζ₃):ℚ] = 2).
- `IsTotallyComplex` API — `InfinitePlace/TotallyRealComplex.lean` (`IsTotallyComplex.finrank`:237 etc.).
- Infinite Galois correspondence — `FieldTheory/Galois/Infinite.lean` (`fixedField_fixingSubgroup`:84,
  `fixingSubgroup_isClosed`:63) + FLT `AbsoluteGaloisGroup.lean` (`localInertiaGroup`:167, `map`:75).
- `Matrix.card_GL_field` (`GeneralLinearGroup/Card.lean:89`); FLT `unipotent` helpers
  (`FLT/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`).
- Dickson (not needed; available): `FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean:54`.
- Kummer/Hilbert 90: `FieldTheory/KummerExtension`, group-cohomology Hilbert 90.
- **Definitively absent** (agents confirmed): ramification filtration, Fontaine bound, group schemes (Hopf
  only), tame-different upper bound, mod-ℓ cyclotomic surjectivity, finite-image→number-field packaging.

## 8. Counterexamples and coefficient-field risks

- **R-1 (soundness, resolved):** trivial-*sub* orientation is false — Kummer-2 peu-ramifiée module (§2).
  Blueprint prose erratum. Lean statement stands.
- **R-2 (soundness hole, NEW — must be closed by any design):** without cyclicity of the I₂-image, e₂ can a
  priori be 9 (elementary abelian ⊆ (k,+), |k| = 3^r), and then rd ≤ 2^{8/9}·3^{3/2} ≈ 9.62 > 8.25 (even > the
  9.3 "beefed-up" Poitou constant): **I-1 fails**. Fix = S11 (unique cubic totally-tame extension over ℚ₂^{ur},
  producible via unit-cube surjectivity + Hensel). The incumbent design does not mention this.
- **R-3 (design-level counterexample):** field-level discriminant bounds *cannot* prove R-2-splitting:
  ℚ(ζ₃, 2^{1/3}) (LMFDB 6.0.34992.1, |d| = 2⁴·3⁷, v₃(d)/n = 7/6 < 3/2) is simultaneously the cut-out field of a
  genuinely flat R-1 module and of the would-be nonsplit R-2 module. Orientation lives in the module, not the
  field ⇒ N1 alone can never discharge R-2; N2 (or equivalent module-level input) is irreducible.
- **R-4 (coefficient field):** k = 𝔽_{3^r} general. Do not use |GL₂(𝔽₃)| = 48, SL₂(𝔽₃), or fixed subgroup
  lists: nonsplit-Cartan images are cyclic of order dividing 3^{2r} − 1, unbounded. The §3 split is uniform in
  k; no Frobenius-semilinear descent is used anywhere (improvement over incumbent C0 worry). Kummer target is
  (ℚˣ/(ℚˣ)³) ⊗ k with k-linear independence — spans, not single classes.
- **R-5 (p = 3 pitfalls):** flat ⟺ peu ramifiée (v₃(class) ≡ 0), but *unramified* needs class ≡ cube mod 9 —
  at p = 3 unit classes can be wildly ramified while flat. Never conflate flat with unramified-at-3.
- **R-6 (numeric fragility):** margin 8.25 − 8.2484 ≈ 0.0016. All inequalities must be stated with the integer
  certificates (2⁴·3⁹ < 33⁶/4⁶; 2·v₃ ≤ 3n − 1), never with floating intermediates.
- **R-7 (Mathlib trap):** `abs_discr_ge` (weak form) silently fails for I-2 at every degree; only
  `abs_discr_ge'` works. A build that "finds a Minkowski lemma" may find the wrong one and dead-end late.

## 9. First buildable tranche

Tranche 1 (§6): S1–S6 pure-algebra pack, one module, zero new axioms, no Galois infrastructure, statable
against frozen types today. Completion audit: builds at pinned toolchain; `#print axioms` for every S-lemma
⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`/`knownin1980s`. This matches and
extends the incumbent's "Slice A" (its `charThree` lemma = S1) but adds the entire case-elimination algebra.
**Do not start Tranches 2–4** before gates G1/G4 clear.

## 10. Completion and stop-loss gates

**Completion (component closes when):** `mod_three` has the frozen type, builds, and `#print axioms` is exactly
⊆ {propext, Classical.choice, Quot.sound, `Odlyzko_statement`, `Fontaine_statement`, `FlatLocalSplit_statement`}
— no `sorryAx`, no `knownin1980s`, no other custom axiom; source-condition reconciliation notes written for
N0/N1/N2 in the axiom docstrings; monitor rows `FLT-FONTAINE-ODLYZKO` → proved-at-T2, `FLT-MOD3` admitted →
proved; blueprint erratum (§2) filed.

**Stop-losses:**
- **G1 (axiom authorization, HARD):** `historical-assumptions.ndjson` currently authorizes zero T2 axioms
  (`HIST-UNRESOLVED` guard). N1 and N2 require the human agreement gate (ladder README). No Tranche-2+ work
  before sign-off. Halt if the operator declines either axiom (then the component is T3-scale: formalize
  Fontaine/Oort–Tate — different program).
- **G2 (orientation):** resolved (§2); reopen only if the R-2 Kummer computation surfaces a nonzero surviving
  class (it must not: the span-injectivity proof is decidable-checkable — if it fails, `mod_three` is false and
  the verdict flips to OBSTRUCTION).
- **G2′ (NEW, e₂-cyclicity):** if S11 cannot be produced within its budget (ℚ₂^{ur} infra too thin), stop:
  I-1 is unsound without it. Fallback: extend N1's source review to cover a tame-inertia-structure axiom —
  operator decision, not a silent widening.
- **G3 (infra):** before Tranche 3, probe-check (small `#check` file): tame-different upper bound presence,
  differentIdeal localization, `abs_discr_ge'` exact form at pinned rev. If D or F exceeds 2× its
  difficulty-scaled budget, split it out as its own obligation and re-plan.
- **G4 (source pinning):** N1: verify Théorème A's constant e(n + 1/(p−1)) and derive the v₃(𝔡) < 3/2 corollary
  in the docstring, page-referenced. N2: pin one exact pre-1990 numbered statement (Oort–Tate 1970 / Mazur 1977
  §I / Fontaine 1985) before the axiom lands; if none matches the k-coefficient form verbatim, the docstring
  must carry the (short) reduction argument. If no pre-1990 locator exists, N2 is not "historical" — halt.

## 11. DoR checklist

- [x] Primary sources identified with exact locators (Poitou p.17 eq.26; Fontaine 1985 Thm A; Oort–Tate 1970 /
      Mazur 1977 — N2 pin pending, gate G4)
- [x] Hypothesis translation: `IsHardlyRamified` fields mapped to classical conditions, incl. Hopf-flatness
- [x] Proof outline complete and case-exhaustive (§3), orientation question resolved with counterexample
- [x] Sublemma graph with build order (§6) and dependency closure (mod_three ← {N0,N1,N2} ∪ S1–S14 ∪ D,E,F)
- [x] Counterexample review done (§8), incl. two adversarial findings vs the incumbent design
- [x] Library matches verified against pinned Mathlib (§7), incl. one wrong-lemma trap flagged
- [~] Lean signatures: Tranche 1 final; N1/N2 and D/E/F signatures drafted, to be frozen at their own stage-1s
- [ ] T2 axiom authorization for N1, N2 (operator gate — BLOCKING)
- [ ] Infra probe results for G3 (cheap, read-only `#check` file)
- **DoR: BLOCKED** for the whole component (consistent with control plane); **READY** for Tranche 1 only.

## 12. Disagreements with the incumbent stage-1 (`stage-1-opus48-primary.md`)

1. Its N2 (small-degree discriminant minima tables) is unnecessary and violates the no-tables constraint —
   I-2/I-3 close with Mathlib Minkowski + Sylow/Kolchin/A₄.
2. Its N3 (Dickson axiom) is unnecessary — no projective-image analysis needed; and the repo already *proves*
   Dickson, so axiomatizing it would be strictly wrong at T2.
3. Its "A₄ degree-12 exceptional case" is vacuous: A₄ has no faithful 2-dim rep in char ≠ 2 (3-line det-parity
   argument); projective-A₄ preimages have order ≥ 24 and land in the Odlyzko branch.
4. Its open G2 (orientation) is resolved here: Lean statement true, blueprint prose erratum, explicit
   counterexample for the other orientation.
5. It misses the e₂ = 9 soundness hole (§8 R-2) — its discriminant budget at 2 is unproved as stated.
6. Net axiom count drops from its 4 (N0 + 3 new) to 3 (N0 + 2 new), with N2 strictly local and minimal.

## 13. Verification plan (for whoever executes)

- Tranche 1: `lake build` the new module; run `FLTMethodology/Probes`-style `#print axioms` audit per lemma.
- Numeric lemmas: `norm_num` closes 2⁴·3⁹ < 33⁶/4⁶; S6b by induction with `(1+1/n)^{2n} ≥ (5/4)^8` at base.
- G3 probe file: `#check NumberField.abs_discr_ge'` exact statement, `differentIdeal` localization search,
  grep for tame-different lemma at pinned rev.
- Control plane: append attempt record to `fontaine-odlyzko/stage-1-attempts.md`; update `source-design.ndjson`
  DoR fields only after G1/G4 outcomes (not edited in this read-only review).

*Read-only review: no repository files were modified. This document is the sole artifact.*
