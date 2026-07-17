# Provenance & simplification — quaternion stabiliser finiteness

**Obligation** `FLT-HIST-QUATERNION` · **component** `quaternion-boundary` · **assurance** T2
(named boundary, *not* a Lean proof) · **disposition** authorized by operator 2026-07-17.

> Reviewer-side source of truth (repo: `helios-control`). Intended in-repo location, placed by the
> FLT loop under the apply prompt, so the axiom docstring can reference it with a clean relative
> path: `methodology/review/flt-completion/quaternion-boundary/stage-4-provenance-disposition.md`.
> This document is self-contained: an expert should be able to judge the axiom's legitimacy from it
> alone.

---

## 1. What is axiomatised

For a totally real number field `F`, a **totally definite** quaternion algebra `D/F`, a **compact**
level `U ⊆ GL₂(𝔸ᶠ[F])`, and any `g ∈ GL₂(𝔸ᶠ[F])`, the arithmetic stabiliser

```
Γ_g  :=  (U · 𝔸ᶠˣ  ∩  g⁻¹ Dˣ g) / Fˣ
```

is **finite** — equivalently `Subgroup.IsFiniteRelIndex 𝓕ˣ ((U ⊔ 𝔸ᶠˣ) ⊓ toConjAct g⁻¹ • 𝓓ˣ)`.
This discharges the consumer `isFiniteRelIndex_Δ` (`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`),
replacing the generic `knownin1980s`. The scalar containment `𝓕ˣ ≤ Δ` is already proved
(`LevelStruct.range_units_le_range`); only the finiteness of the quotient is named here.

## 2. Disposition in one line

This is a **modern-synthesis T2 axiom**: it names a statement whose *faithful* source is modern
(Voight 2021), because — as established below — no single pre-1990 primary theorem states it in this
adelic packaging. It is **not** a pre-1990-historical axiom, and it is **not** a proof of the
finiteness in Lean. What it buys: the obligation is no longer blocked on a citation that does not
exist, no longer carries a false pre-1990 attribution, and no longer carries a redundant hypothesis.

## 3. Why the block is correctly cleared — the provenance verdict

The source gate blocked because it demanded a page-exact **pre-1990** primary theorem covering both
the adelic-to-order construction and the exact scalar-kernel quotient, and the loop could not supply
one. Three independent deep-research reviews were commissioned. Their finding is unanimous on the
decisive point:

| Review | Verdict | Route it took |
|---|---|---|
| GPT-5.6-xhigh | **(b)** short pre-1990 chain suffices | Borel 1963 §1.2 + Vignéras II.1.1, **via the adjoint representation** — bypasses orders entirely |
| Gemini Pro | **(c)** modern synthesis | Vignéras 1980 Ch. III + Ch. V chain / Voight 2021; recommends the Borel–Harish-Chandra topological bypass of orders |
| Claude | **(c)** modern synthesis | Fujisaki 1958 / Weil 1967 + Vignéras III.1.4 + V.1; earliest *single-theorem* source Voight 2021 Main Thm 27.6.14 |

- **No single pre-1990 primary theorem** states `Γ_g` finiteness in this adelic packaging. The
  classical literature bifurcates it (adelic parameterisation via strong approximation on one side;
  order-unit finiteness on the other); the packaged statement is post-1970s Langlands-era language.
- The **(b) vs (c) split is a labelling choice**, not a factual disagreement: is "a chain of
  pre-1990 results + the author's own gluing" a pre-1990 *provenance*, or a *modern synthesis*? Both
  are defensible. On the facts all three agree.
- **Faithful modern source** (what an honest citation uses): Voight, *Quaternion Algebras*, GTM 288
  (2021), **Main Theorem 27.6.14** (Fujisaki's lemma), with order-unit endpoint **Lemma 26.5.1 /
  17.7.13** — already registered in the repository as `SRC-017` / `SRC-022`. Decisive precedent: the
  **Buzzard–Taylor FLT blueprint itself proves this** and cites Voight, not a pre-1990 theorem. So
  axiomatising from the modern source *matches upstream practice exactly*.

The gate was not being pedantic. It caught a genuine anachronism, and the honest resolution is to
cite the source that genuinely states the result, flagged as a modern synthesis.

## 4. The simplification — the adjoint-representation route

Two of the three reviews (GPT and Gemini) **independently** arrived at a proof architecture markedly
simpler than the order-theoretic route the loop's stage-1 designs took. It is the recommended
justification, and the recommended shape of a future T3 Lean proof.

Let `Ad : Dˣ → GL_F(D)`, `d ↦ (x ↦ d x d⁻¹)`.

1. **Exact scalar-kernel bridge (no square-class detour).** `D` is central simple over `F`, so
   `ker(Ad) = Z(D)ˣ = Fˣ` *exactly*. Hence `Dˣ/Fˣ ↪ GL_F(D)` injectively, and the `/Fˣ` quotient in
   `Γ_g` is *precisely* the kernel of `Ad`. This removes the stage-1 hazard flagged in Opus §6: the
   map `Δ_g/Fˣ → 𝒪¹` fails unless the reduced norm is a square. The adjoint route never forms `𝒪¹`,
   never touches the square-class quotient `Rˣ/(Rˣ)²`, and never constructs an order.

2. **The non-compact scalar factor dies.** `𝔸ᶠˣ` is central in `(D⊗𝔸ᶠ)ˣ`, so `Ad(u·z) = Ad(u)` for
   any finite idele `z`. Therefore the image of `U·𝔸ᶠˣ` under `Ad` is just `Ad(g U g⁻¹)`, which is
   **compact** whenever `U` is compact. This is the crux the packet worried about (`UA = U ⊔ 𝔸ᶠˣ` is
   *not* compact, because `𝔸ᶠˣ` is not) — the adjoint quotient is exactly what tames it, with no
   norm-one gymnastics.

3. **Compact archimedean image (Vignéras II.1.1).** Total definiteness ⇒ each real completion
   `D_v ≅ ℍ` (Frobenius / Vignéras II.1.1). For Hamilton's quaternions `Ad(ℍˣ) = ℍˣ/ℝˣ ≅ SO(3)`,
   compact (polar form `ℍˣ = ℝ_{>0} × SU(2)`; `Ad` kills `ℝ_{>0}` and `±1`, leaving `SU(2)/{±1} =
   SO(3)`). So `K_∞ = ∏_{v∣∞} SO(3)` is compact. *This is the only place total definiteness is used.*

4. **Discreteness (Borel 1963 §1.2).** `Dˣ/Fˣ`, the `F`-points of the adjoint group, is **discrete**
   in its adelic points (Borel, *Some Finiteness Properties of Adele Groups over Number Fields*,
   Publ. Math. IHÉS 16 (1963), §1.2, p. 7).

5. **Finish.** `Ad(Γ_g) ⊆ Ad(Dˣ/Fˣ) ∩ (K_f × K_∞)` with `K_f = Ad(gUg⁻¹)` and `K_∞` both compact. A
   discrete subset meets a compact set in finitely many points (locally compact Hausdorff). Hence
   `Γ_g` is finite. ∎(sketch)

**What this route avoids that the order route needed:** the adelic-to-order dictionary, strong
approximation, Eichler/maximal orders, the norm-one unit group `𝒪¹`, and the square-class quotient.
It uses only two inputs — the adjoint kernel identity and Borel discreteness — plus the one-line
compactness of `SO(3)` from total definiteness.

> **Status of this argument.** It is the reviewers' proof *architecture*, independently corroborated,
> not itself a Lean proof. The exact statements of Borel §1.2 and Vignéras II.1.1 are checkable; the
> **gluing (steps 1–5) is the author's own** and is what a T3 proof must formalise (see §7). For the
> T2 axiom it is the justification of legitimacy — an expert can see the statement is true and
> standard — not a discharge of it.

## 5. Hypothesis minimisation — openness dropped

The stage-1 signature carried `hUo : IsOpen U`. **All three reviews independently conclude it is
redundant** for `Γ_g` finiteness; `hUc : IsCompact U` alone suffices. The mechanism is §4 above:
finiteness rides on `Ad(gUg⁻¹)` being compact, which needs only compactness of `U`.

This also **resolves a contradiction internal to the loop's own artifacts**: Opus stage-1 §4 asserted
openness is required, justifying it with "taking `U = ⊤` invalidates the result." But `⊤` is already
excluded by *compactness* (`GL₂(𝔸ᶠ)` is not compact, so `⊤` is not a compact subgroup) — the `U = ⊤`
counterexample says nothing about openness. The stage-3 packet then suspected `hUo` redundant. Three
external reviews break the tie in favour of the packet.

Openness *is* load-bearing elsewhere — for the finiteness of the whole double-coset set
`Dˣ \ (D⊗𝔸ᶠ)ˣ / U` (openness makes that quotient discrete) and for the downstream smooth/Hecke
structure — but that is a **different statement** this lemma does not assert. Dropping `hUo` makes the
axiom strictly more general, so the consumer (which supplies `ℒ.isOpen_U`) still discharges.

**Guard (a STOP condition in the apply prompt):** the drop is a mathematical claim, not a sourced
fact. Before landing it, verify in Lean that no declaration reached *from this obligation* consumes
`U`-openness through it. If one does, halt and re-scope. This is the single condition all three
reviews attached.

## 6. Citations, with reliability labels

**Load-bearing / checkable (cite these):**

- Voight, *Quaternion Algebras*, GTM 288 (2021), Main Thm 27.6.14; Lemma 26.5.1; Lemma 17.7.13.
  Registered `SRC-017` / `SRC-022`. Faithful modern source; used by the FLT blueprint itself.
- A. Borel, *Some Finiteness Properties of Adele Groups over Number Fields*, Publ. Math. IHÉS **16**
  (1963), §1.2, p. 7 — discreteness of `G(F)` in `G(𝔸)`.
- M.-F. Vignéras, *Arithmétique des algèbres de quaternions*, LNM **800** (1980), **II.1.1**,
  pp. 31–32 — a real-ramified completion is `ℍ` (compact adjoint).

**Classical lineage, decimals UNVERIFIED — do NOT print as verified:**

- Vignéras LNM 800, Ch. III fundamental theorem (cited variously as "III.1.4" and "Théorème
  fondamental 4, §5", p. 61) — strong approximation / adelic-to-order dictionary.
- Vignéras LNM 800, Ch. V §1–2 (cited variously as "V.1.2, p. 139" and "Cor. V.2.5, p. 143") —
  order units finite modulo centre.
- G. Fujisaki (1958), Thm 8.3 (quoted via Voight, original not inspected); A. Weil, *Basic Number
  Theory* (1967), Ch. IV / XI (section-level only).

The three reviews disagree on these decimals (same Vignéras theorems, different numbers) and each
review states it could not verify them from primary text. They are recorded here as lineage, **not**
as load-bearing citations. Resolving them requires one person to open Vignéras LNM 800 — which is not
necessary to justify the axiom, since the checkable modern source suffices.

## 7. What a T3 Lean proof must discharge

If/when this axiom is promoted to a proof, the adjoint route (§4) reduces it to:

1. `ker(Ad : Dˣ → GL_F(D)) = Fˣ` for `D` central simple over `F` (algebra, no analysis).
2. `Ad(ℍˣ) ≅ SO(3)` compact, hence `K_∞ = ∏_{v∣∞} SO(3)` compact from total definiteness.
3. Finite-adelic scalars act trivially under `Ad`, so `Ad(U·𝔸ᶠˣ) = Ad(gUg⁻¹)` compact from `hUc`.
4. `Dˣ/Fˣ` discrete in its adelic points (Borel §1.2).
5. discrete ∩ compact = finite (point-set topology in a locally compact Hausdorff group).

Steps 1 and 5 are library-level; 2–4 are the substance. This is a **shorter** obligation ladder than
the order-theoretic route (which additionally needed strong approximation, order construction, and
the norm-one/square-class analysis).

---

*Reviewer: `agent:claude`, cockpit reviewer side. VERIFY ≠ PRODUCE — this dossier recommends and
records; it does not author, register, weaken, or mark the gate. The operator holds the T2
authorization; the FLT loop applies the edit; the source gate and `#print axioms` re-check.*
