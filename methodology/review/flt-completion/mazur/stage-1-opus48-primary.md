# Opus 4.8 primary design — Mazur

- Component: `mazur`
- Obligation: `FLT-HIST-MAZUR`
- Stage: primary T2 name-source design
- Agent: `opus48-primary-designer-d10`
- Backend/model: `claude-code` / `claude-opus-4-8`
- Permission mode: `suggest` (read-only requested)
- Scheduled difficulty/budget: `10` / `3600s`
- Transport result: `SUCCESS`
- Actual elapsed: `578365ms` (`real 578.34s` from `/usr/bin/time`)
- Claude session: `93ee28d0-26e7-4d49-b0e2-59ec85ac27ab`
- Unique request IDs: `13`
- Token telemetry, deduplicated by `requestId`: `15102` input, `72738` cache creation,
  `485059` cache read, `33502` output (`606401` total including cache tokens)
- Verdict: **READY-FOR-GPT-REVIEW**
- Promotion: none; GPT review and the human axiomatization gate remain mandatory

> **Post-review correction.** The final paragraph of §6 claiming a broader semistable/full-
> two-torsion statement is false was rejected by the independent GPT-5.6 review and is not
> load-bearing. It is retained below only as raw producer history. The authoritative disposition is
> `stage-2a-review-disposition.md`; no registered justification may repeat that claim.

The bridge's final response summarized the report and pointed to Claude's automatically generated
plan cache. The complete report below is preserved from that cache so the authorized repository
artifact contains the full model deliverable. The model made no FLT repository edits.

Deduplicated request IDs:

```text
req_011Cd7ExMS53GnkAVrHrwUPQ
req_011Cd7F4jGPxqHFj44KAG8DH
req_011Cd7F51UxwmURMsTdhyANd
req_011Cd7F5J47yiFun4rX4G6Mx
req_011Cd7F7xUikEUpJVEkvkoBj
req_011Cd7F8RnYLHgiqoemJP7ZP
req_011Cd7F8t6KooGffMFjXwnkm
req_011Cd7FDRRbdpW1g12nbraez
req_011Cd7FEMtoA5QJ12n4FLZhL
req_011Cd7FHZ9ZCLarekMxZ75wQ
req_011Cd7FNq696oMCXDXoNbFFG
req_011Cd7FeyuQf1MqryRyHMZCb
req_011Cd7FfL38SmkF7ixb49xKW
```

## Context

`FreyPackage.mazur` is the last generic `knownin1980s` boundary on the FLT critical spine that
carries irreducibility of the Frey curve's `p`-division Galois representation. T1 deliberately
leaves it as the universal escape-hatch axiom. The T2 obligation is to replace that generic
authority with one exact, named, source-faithful finite assumption that elaborates against the
unchanged consumer, has a precise primary-source locator, and is neither `knownin1980s` renamed nor
a stronger/unrelated claim. The concrete `galoisRep` construction is already kernel-clean
(`FLT-TORSION-001`), so only this named historical input remains.

Prompt baseline note: the prompt froze `827eb96`; the run inspected working HEAD `66e4f1e` on
`methodology/varro-proof-program-20260716`.

## 1. CURRENT CONSUMER BOUNDARY

`FreyPackage.mazur`, `FLT/FreyCurve/Mazur.lean:30-36`:

```lean
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  knownin1980s
```

- `E := P.freyCurve` and `p := P.p` are definitionally transparent lets.
- The statement creates `Fact p.Prime` from `P.pp`.
- The goal is concretely
  `GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos)`.
- The current body uses the universal `knownin1980s {P : Prop} : P`; the type exists, but the proof
  does not.

Supporting definitions are the kernel-clean `WeierstrassCurve.galoisRep`,
`GaloisRep.IsIrreducible`, `FreyPackage`, and `P.hppos`.

The only direct consumer is `exact P.mazur` at `FLT/Proof.lean:97`, inside `B4_implies_B3`. The path
to the top theorem is:

```text
FreyPackage.mazur
  -> B4_implies_B3
  -> B3_proof
  -> B2_proof
  -> B1_proof
  -> flt
```

The top theorem currently also contains `sorryAx` from the separate
`FreyCurve.torsion_not_isIrreducible`/Ribet-Wiles obligation; this design addresses only the Mazur
`knownin1980s` boundary.

## 2. PRIMARY SOURCE LOCATOR

The exact terminal source is J.-P. Serre, *Sur les représentations modulaires de degré 2 de
Gal(Qbar/Q)*, Duke Math. J. 54 (1987), 179-230, DOI `10.1215/S0012-7094-87-05413-5`, §4.1,
Proposition 6, printed p. 201 (`SRC-020`). It treats
`y² = x(x-A)(x+B)` for pairwise-coprime nonzero `A,B,C` with `A+B+C=0`, the stated parity
normalization, and prime `p >= 5`, and concludes that the representation on `p`-division points is
irreducible. This directly matches the repository's Frey-shaped curve
`Y² = X(X-a^p)(X+b^p)`.

Load-bearing ingredients inside Serre's proof, relevant to a future T3 proof but not separate T2
names here, are:

- Serre 1972, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*, Invent.
  Math. 15, Lemmas 5-6, p. 307 (`SRC-021`), giving the semistable reducible-character dichotomy.
- Mazur 1977, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47, Theorem 8,
  pp. 35-36 (`SRC-006`), giving the rational-torsion classification and bound 16.

Mazur's torsion theorem and the existing `Mazur_statement` do not have the irreducibility type and
cannot directly discharge this consumer. Serre Proposition 6 consumes Mazur's result and supplies
the exact terminal conclusion. The faithful T2 source is therefore Serre 1987, specialized to
`FreyPackage`.

## 3. MINIMAL NAMED T2 INTERFACE

Recommended name and exact signature:

```lean
/-- Serre 1987, Duke Math. J. 54, §4.1 Proposition 6. -/
axiom Serre1987.freyCurve_galoisRep_isIrreducible (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos)
```

The unchanged consumer can then be a one-line term proof:

```lean
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) :=
  Serre1987.freyCurve_galoisRep_isIrreducible P
```

This consumes only existing kernel-clean `FreyPackage`, `freyCurve`, `galoisRep`,
`IsIrreducible`, and prime facts. It contains no generic `Prop`; it can prove only this exact Frey
irreducibility statement and carries an exact primary locator. It also avoids the `Set.ncard`
infinite-set weakness in `Mazur_statement`.

The human gate must decide whether the axiom is co-located in `FLT/FreyCurve/Mazur.lean` under the
recommended namespace/name, or placed in a dedicated `FLT/Assumptions/Serre.lean` module with a
register-consistent alternative name.

## 4. HYPOTHESIS TRANSLATION AND MINIMALITY

Serre's hypotheses translate as follows:

| Serre hypothesis | Repository data |
|---|---|
| `A+B+C=0`, with `A=a^p`, `B=b^p`, `C=-c^p` | `P.hFLT` |
| pairwise coprime and nonzero | `P.ha0`, `P.hb0`, `P.hc0`, `P.hgcdab`, and derived `hgcdac`/`hgcdbc` |
| parity normalization | `P.ha4`, `P.hb2` |
| prime `p >= 5` | `P.pp`, `P.hp5` |
| exact curve model | `P.freyCurve` |
| semistability | proved `freyCurve_isSemistableOverQ` |
| full rational 2-torsion | proved `freyCurve_hasFullRationalTwoTorsion` |
| rational torsion bound 16 | Mazur Theorem 8, internal to Serre's proof |

Every retained datum is already contained in `(P : FreyPackage)`, so the specialized axiom needs no
extra hypothesis. Semistability and full 2-torsion are proved consequences; the Mazur bound is an
ingredient of the cited proof. The conclusion is exactly irreducibility for this Frey curve, not a
general semistable-curve theorem or an unrelated torsion/modularity result.

The human source gate should explicitly check the parity nuance sometimes stated as
`b ≡ 0 mod 32` versus the repository's `b` even field. The repository's own semistability provider
and source packet treat the specialization as valid, but this detail deserves sign-off.

## 5. DEPENDENCY AND AXIOM-SURFACE PATH

```text
Serre1987.freyCurve_galoisRep_isIrreducible
  -> FreyPackage.mazur
  -> B4_implies_B3
  -> B3_proof
  -> B2_proof
  -> B1_proof
  -> flt
```

After registration, `#print axioms` for each reached declaration should name the exact Serre axiom
and no longer name generic `knownin1980s` through this path. `WeierstrassCurve.galoisRep`,
`GaloisRep.IsIrreducible`, `freyCurve_isSemistableOverQ`,
`freyCurve_hasFullRationalTwoTorsion`, and the source/assembly providers must remain standard-axiom
only. The separate `sorryAx` on the Ribet-Wiles side remains until its own obligation closes.

## 6. COUNTEREXAMPLES AND OVERSTATEMENT RISKS

1. A Galois-stable line need not be a rational point; it may carry a nontrivial character.
2. Treating only the trivial stable-line character misses the cyclotomic-line/quotient case.
3. Full 2-torsion is preserved by the relevant odd-degree `p`-isogeny, not by arbitrary isogenies.
4. A nonzero discriminant proves nonsingularity, not semistability; additive reduction remains
   possible.
5. `p=5` is safe because `4p=20>16`; the excluded small-prime cases are genuinely different.
6. Wrong sign/parity normalization changes the model and local reduction at 2.
7. `Set.ncard` is zero on infinite sets, so deriving irreducibility solely through the existing
   `Mazur_statement` requires a separate finiteness proof.

A broader axiom claiming every semistable curve with full rational 2-torsion and `p>=5` has an
irreducible representation is false: semistable curves with rational `p`-isogenies exist. The
source-faithful boundary must remain specialized to the Frey shape/package.

## 7. SIGNATURE PROBE PLAN — NOT RUN

```lean
import FLT.FreyCurve.Mazur
import FLT.Proof

axiom Serre1987_freyCurve_galoisRep_isIrreducible_PROBE (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos)

example (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) :=
  Serre1987_freyCurve_galoisRep_isIrreducible_PROBE P

#check @Serre1987_freyCurve_galoisRep_isIrreducible_PROBE
#print axioms Serre1987_freyCurve_galoisRep_isIrreducible_PROBE

theorem mazur_via_named_PROBE (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) :=
  Serre1987_freyCurve_galoisRep_isIrreducible_PROBE P

#print axioms mazur_via_named_PROBE
```

This probe was not run. Its signature is character-for-character identical to the existing
elaborating theorem's type, so signature risk is low, but the human gate must run the probe and
then audit the real `FreyPackage.mazur` and `flt` declarations after any registration.

## 8. VERDICT — READY-FOR-GPT-REVIEW

The design is `READY-FOR-GPT-REVIEW` (the inherited sub-prompt's `NAMEABLE`). Serre 1987 §4.1
Proposition 6, p. 201 supplies an exact primary-source locator, and the proposed signature is
identical to the real consumer type. The design rejects the unrelated/weaker `Mazur_statement` and
the false general-curve abstraction. The human gate must still approve the name/placement, parity
source nuance, and eventual registration after elaboration and axiom-surface probes. No axiom was
registered and no T3 proof was claimed.

## Human-gate action list — not executed

1. Confirm the axiom name and placement.
2. Run the signature and consumer probes, then confirm `#print axioms` loses `knownin1980s` on the
   intended path.
3. Correct the obligation's source refs to include `SRC-020`/`SRC-021` and stop advertising
   `Mazur_statement` as the terminal library candidate.
4. Add the approved named axiom to the T2 permitted-axiom surface only after human acceptance.
