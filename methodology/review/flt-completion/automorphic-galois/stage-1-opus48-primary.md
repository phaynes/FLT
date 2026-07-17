# Opus 4.8 primary early-interface design — automorphic–Galois

- Component: `automorphic-galois`
- Obligations: `FLT-AUT-GALOIS`, `FLT-SUPPORT-AUTOMORPHIC`, `FLT-RACAR-DEF`
- Agent/model: `opus48-primary-designer-d10` / `claude-opus-4-8`
- Backend/permission: `claude-code` / `suggest` (read-only requested)
- Difficulty/budget: `10` / `3600s`
- Attempt 1: `CANCELLED / NO VERDICT`; `320250ms`; session
  `2e3dafde-f92b-4d13-bb1e-2240274b0c3b`; `44` unique request IDs; `29487` input,
  `254049` cache creation, `1961745` cache read, `4215` output (`2249496` total including cache)
- Attempt 2 transport: `SUCCESS`
- Attempt 2 elapsed: `567052ms` (`real 567.06s`)
- Attempt 2 session: `a5754825-be5a-4ce7-8269-36d80330d1dc`
- Attempt 2 unique request IDs: `40`
- Attempt 2 tokens: `30017` input, `275851` cache creation, `1834816` cache read,
  `27852` output (`2168536` total including cache)
- Verdict: **OBSTRUCTION**
- Promotion: none; the component remains dependency-gated

Attempt-2 request IDs, deduplicated across the primary Claude session and its subagents:

```text
req_011Cd7SPRDG3gDJw4x5AV42L
req_011Cd7SQs1pJnBcG43ot9E4f
req_011Cd7SRWcG67MiB8Pi4ZTKf
req_011Cd7SRXSsCSUd9n2XrscGm
req_011Cd7SS4DnghCcRDE21VfBq
req_011Cd7SS4SS3SYKbiVdYSBBR
req_011Cd7SSCmVPEcZiVMdrv3qs
req_011Cd7SSETCBkHkKJYsHz7MC
req_011Cd7SScj8wxD2VB9bpojMk
req_011Cd7SSwmNeVBCovJnwX3rm
req_011Cd7SSy51FKrsAVNaCZ3Pk
req_011Cd7ST2WNxAXQHKx5Kdm5y
req_011Cd7STXkGvwFJyW3Ek6z8U
req_011Cd7STodzpGGtKVui24EK7
req_011Cd7SU8CTXCJXsTDJWmVSJ
req_011Cd7SUYoZCiftTiZSro6wM
req_011Cd7SUa2DuxTGafGi65iRJ
req_011Cd7SUcZGtSBxY1gh2BHBU
req_011Cd7SVH8G3xRrwy51rVQis
req_011Cd7SVStswey5CEvgQUvay
req_011Cd7SVqsVnfzP44TiTncvw
req_011Cd7SVwnCd6tenMM5zVkfS
req_011Cd7SWSJSVs4x2EBTMHJF1
req_011Cd7SWUCHrkRFx4WqP9dRa
req_011Cd7SWeZswJgQG5MP6d1Y6
req_011Cd7SXLFpx1VM3mjrgiJ8Q
req_011Cd7SXbPR67u2kyHegkV2V
req_011Cd7SXsJsgm19WJf3yGmfu
req_011Cd7SYXeiP4M6b6bjhxaXB
req_011Cd7SZFaMdHXbj6EFRcQEX
req_011Cd7SZUcBRJpbo9C3W8ucj
req_011Cd7SaZa7BrEW2Nu7ZKP6g
req_011Cd7SeCr39cBN7iz4CXsfH
req_011Cd7SfVwxqZsRwBdgArq3A
req_011Cd7SgKZukDkgRW9AC811B
req_011Cd7SpDm8hTUPecB5uJ6PU
req_011Cd7Sqn5bx9CuhjybJvKMG
req_011Cd7SrMkeY9bMPosr4AHLs
req_011Cd7T4Kfy46611LgP4saZn
req_011Cd7T5zLBxbya9VYCfeoBZ
```

## Verdict — OBSTRUCTION

A source-faithful, non-circular, non-generic-axiom interface for this component cannot be frozen
now. The obstruction is concrete and enumerable:

1. The selected source requires Hodge–Tate weights under a coefficient embedding, crystallinity,
   and a Fontaine–Laffaille interval. This vocabulary is absent from the frozen Mathlib/FLT
   surface. `GaloisRep.IsFlatAt` must not be substituted for these conditions.
2. Automorphic-to-Galois attachment is itself a deep cited Carayol–Taylor / Blasius–Rogawski input.
   A generic `forall RACAR, exists rho` axiom is forbidden, while a source-faithful guarded version
   cannot yet state the required ramified local-global compatibility because Weil–Deligne/local
   Langlands vocabulary is absent.
3. `MLT-SOURCE-CONTRACT.md` already records this stop point and orders coefficient and p-adic-Hodge
   interfaces before RACAR and the selected MLT source contract.

What can be banked without closing an obligation is a RACAR data-only skeleton, an exact support
reachability manifest, and an AUT-GALOIS interface-shape/axiom-policy record.

## Existing reusable surface

- `GaloisRep.IsAutomorphicOfLevel` encodes good-prime unramified Frobenius matching only; it is not
  the source's full local-global compatibility conclusion.
- The Galois representation API supplies localization, Frobenius characteristic polynomials,
  determinant, base change, conjugation, irreducibility, and unramified/flat predicates.
- Compatible families supply weak Frobenius-characteristic-polynomial compatibility.
- Quaternionic automorphic forms, level structures, Hecke operators, eigenforms, and quaternion
  algebra classes exist.
- `cyclic_base_change` remains admitted and cannot be used as a proved interface input.

Missing are a totally-real GL2 RACAR type, an attached-Galois-representation construction,
Hodge–Tate/crystalline/Fontaine–Laffaille vocabulary, ramified local Langlands/Weil–Deligne
compatibility, and Jacquet–Langlands.

## Source-hypothesis status

Taylor 2018 Theorem 2.1.1 requires:

| Source hypothesis | Required interface | Current state |
|---|---|---|
| RACAR `π` over `F` | `FLT.Automorphic.RACAR` | absent |
| semisimplified residual match | coefficient reduction/lattice package | absent |
| matching Hodge–Tate weights | p-adic-Hodge interface | absent |
| residual irreducibility after cyclotomic restriction | irreducibility plus residual layer | partial |
| `ell` unramified in `F` | number-field ramification | expressible |
| crystalline at every `v | ell` | crystalline predicate | absent |
| `π_v` unramified at every `v | ell` | RACAR local components | absent |
| Fontaine–Laffaille weight interval | weight/interval vocabulary | absent |

Six of the eight hypotheses cannot presently be stated faithfully.

## Bankable contract A — RACAR data skeleton

The RACAR object must be pure data and must not mention an attached `GaloisRep`. A provisional
global skeleton may expose a coefficient field, an automorphic eigensystem placeholder, and a finite
ramification/level set. Hodge–Tate weights and local components must remain deferred until their
actual types exist; a `True`-valued placeholder is suitable only for a methodology probe, not a
production definition.

The graph currently omits a load-bearing edge: the RACAR obligation demands Hodge–Tate weights but
depends only on coefficients and automorphic support. The source contract orders
`FLT-MLT-PADIC-HODGE` before `FLT-RACAR-DEF`; that dependency edge must be added and re-derived
before the execution graph can be trusted.

## Bankable contract B — support reachability manifest

`FLT-SUPPORT-AUTOMORPHIC` must not remain an umbrella admission. Its deliverable is a generated
reachability manifest from the selected theorem roots, listing each actually reached admitted
declaration as its own audit target. Off-route admissions must not be closed merely to reduce a raw
count, and no generic `automorphic_support` axiom may replace the umbrella.

## AUT-GALOIS contract shape — not yet elaboratable

The eventual interface must separate:

- RACAR attachment;
- quaternionic attachment;
- coefficient transport and stable lattice/reduction;
- good-prime Frobenius compatibility;
- ramified monodromy/local compatibility; and
- downstream R-to-T assembly.

It should be a witness-indexed existence statement guarded by the complete source hypotheses and
conclude existence of a Galois representation with the required compatibility. It must not consume
the MLT theorem or restate `IsAutomorphicOfLevel` as its conclusion. It cannot yet elaborate because
coefficient, Hodge–Tate/crystalline, and Weil–Deligne fields are absent.

## Dependency order

```text
FLT-HIST-QUATERNION
  -> FLT-SUPPORT-AUTOMORPHIC

FLT-MLT-COEFFICIENTS
  -> FLT-MLT-PADIC-HODGE
  -> FLT-RACAR-DEF
  -> FLT-MLT-SOURCE
  -> FLT-AUT-GALOIS
  -> FLT-HECKE-ACTION / FLT-MLT
```

The `FLT-MLT-PADIC-HODGE -> FLT-RACAR-DEF` definition edge is a required repair, not an established
current graph fact.

## Bounded later work units

1. Generate and review the support reachability manifest.
2. Elaborate a data-only RACAR skeleton that imports no Galois representation and has standard-trio
   closure.
3. Record the AUT-GALOIS shape and axiom-policy decision without pretending it elaborates.
4. Land coefficient/lattice/semisimplification vocabulary upstream.
5. Land Hodge–Tate/crystalline/Fontaine–Laffaille vocabulary upstream.
6. Decide and implement the Weil–Deligne/ramified-LGC vocabulary.
7. Only then consider a fully guarded, named attachment axiom or construction.

## Soundness checks

- No RACAR or attachment declaration may import the desired MLT conclusion.
- No generic support or unconditional attachment axiom is acceptable.
- `IsFlatAt` is not crystalline/Hodge–Tate.
- A bare integral two-dimensional representation is not automatically the source representation;
  residual reduction, semisimplification, and stable-lattice choice are load-bearing.
- Good-prime compatibility is not ramified local-global compatibility.
- RACAR must remain independent of any attached representation.
- Every banked probe must retain only the standard axiom trio.

## Gates before re-review

1. Coefficient and p-adic-Hodge signatures are kernel-green.
2. The missing p-adic-Hodge-to-RACAR graph edge is added and regenerated.
3. The support reachability manifest replaces the umbrella with named audit targets.
4. The operator records whether automorphic attachment is to be constructed or admitted as an exact
   named cited theorem.
5. The project decides whether to formalize ramified Weil–Deligne compatibility or restrict its
   source theorem to a genuinely matching good-prime statement.

Until these gates clear, the honest verdict remains **OBSTRUCTION**, not `READY`.
