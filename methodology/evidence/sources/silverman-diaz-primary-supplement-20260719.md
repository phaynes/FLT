# Silverman and Diaz y Diaz primary-source supplement, 2026-07-19

## Decision

The newly supplied PDFs close two source-access gaps in the 2026-07-19 literature
register. They improve source assurance and proof design, but they do not by
themselves promote a proof obligation or a Lean declaration.

- Search-register SHA-256: `d983048c218d16734a54eefec6ebc9af6537e7bebf27b09b348e4c5de328c621`
- Search-register size: 62,238 bytes
- Trusted FLT base: `1f6d11caee718028bf783c968511d34865ffd9f0`
- Programme effect: source locators and Lean-facing design constraints only
- Lean effect: no `.lean` declaration added, changed, or promoted
- Promotion authority: `may_promote = false`

The register remains a research synthesis rather than a mathematical source. The
findings below come from visual inspection of the cited primary pages.

## Source bytes

| Source | Cached file | SHA-256 | Pages visually inspected |
|---|---|---|---|
| J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves* (1994) | `build/literature-enrichment/cache/Joseph H. Silverman - Advanced Topics in the Arithmetic of Elliptic Curves (1994) [978-1-4612-0851-8].pdf` | `d06410160f5648135b060955e3a937c2f7de2361a02b0782e60ffec49fd49314` | printed pp. 441--447, PDF pp. 453--459; especially Theorem V.5.3 and proof, printed pp. 442--444 |
| Silverman, official *Advanced Topics* errata | `build/literature-enrichment/cache/silverman-ataec-errata.pdf` | `3d524535d7d5d50777b8a0fe66ef290d594effea46dc330b4df2486e8e017b8d` | errata p. 20, corrections for printed pp. 441 and 447 |
| F. Diaz y Diaz, *Tables minorant la racine n-ieme du discriminant d'un corps de degre n* (1980) | `build/literature-enrichment/cache/D_DIAZ_80_06.pdf` | `ee847fd414f0b410bd747d4261717733ca9efee7eed7a9051638534518464916` | Table 1, table p. 1, PDF p. 26 |
| K. Joshi, *Remarks on Methods of Fontaine and Faltings* (1999) | `build/literature-enrichment/cache/joshi-1999.pdf` | `fcc1b126bf676d685e60f1cf9e067b2e5de43521d7b4c7a392339b5c406031a0` | Theorem 4.1 and proof, manuscript pp. 5--6 |

The PDFs are retained only in the ignored build cache. They are not committed or
redistributed by this supplement.

## Silverman V.5.3

### Exact source statement

Silverman assumes that `K` is a p-adic field and that `E/K` is an elliptic curve
with `|j(E)| > 1`. With the official erratum applied, part (a) states that there is a
unique `q` in the algebraic closure with `|q| < 1` for which `E` and the Tate curve
`E_q` are isomorphic over the algebraic closure, and that this unique `q` lies in
`K`.

For that `q`, part (b) proves the equivalence of:

1. `E` is isomorphic to `E_q` over `K`;
2. Silverman's square-class invariant `gamma(E/K)` is trivial; and
3. `E` has split multiplicative reduction.

The proof occupies printed pp. 442--444. It first identifies the Tate parameter
from the `j`-invariant, then proves that the Tate curve has trivial square-class
invariant and split multiplicative reduction, and finally uses the split node and
Hensel lifting to prove the converse over `K`.

### Exact scope and residual gap

- The theorem covers p-adic fields, including residue characteristic 2.
- It does not cover arbitrary equal-characteristic complete nonarchimedean fields.
- It supplies the base-field Tate-form characterization required by the local-form
  portion of `FLT-TATE-UNRAMIFIED`.
- It does not construct the explicit analytic point equivalence; Silverman V.3.1
  or Tate's primary paper supplies that separate input.
- It does not supply the finite-flat torsion scheme or a fully normalized,
  source-faithful Weil pairing. `FLT-TATE-FLAT` and `FLT-TATE-WEIL` remain open.

The exact theorem therefore removes the former visual-source gap but leaves a
scope adapter between a p-adic field and the repository's more general
`IsNonarchimedeanLocalField` signature.

## Diaz y Diaz and Joshi's mod-3 degree bounds

### Primary table rows

Diaz y Diaz Table 1 is explicitly the totally imaginary case. On table p. 1,
PDF p. 26, the inspected rows are:

| Degree `n` | Lower bound for the root discriminant |
|---:|---:|
| 4 | 3.25456113 |
| 22 | 10.25752840 |
| 24 | 10.66833176 |

### First use in Joshi Theorem 4.1

Joshi's mod-3 case forms the field cut out by the representation after adjoining
the mod-3 cyclotomic character. The field contains `Q(zeta_3)`, so it is totally
imaginary and its degree is even. Theorem 2.1 gives a strict root-discriminant
upper bound below 10.39.

The degree-22 lower bound remains below 10.39, while the degree-24 lower bound is
10.66833176. Thus the first even degree excluded by the table is 24, and the source
calculation yields `n <= 22`. Joshi then uses ramification-index divisibility to
reduce to degrees 6, 12, and 18, and excludes 18 because it does not divide
`#GL_2(F_3) = 48`.

### Second use in the order-12 case

In the dihedral order-12 branch, Joshi passes to the fixed field of the normal
3-Sylow subgroup. That degree-4 field still contains `Q(zeta_3)`, is unramified at
2, and is tamely ramified only at 3. The tame bound is strictly below 3. Diaz y
Diaz's totally imaginary degree-4 lower bound is 3.25456113, so such a degree-4
field cannot exist. Equivalently, the table and even-degree condition force degree
at most 2, contradicting the constructed degree 4.

### Exact result and residual gap

The inspected chain is an exact primary-source route to Joshi's stated
nonexistence of an irreducible `F_3` representation satisfying:

- finite flatness at 3;
- semistability at 2; and
- unramifiedness outside `{2, 3}`.

It does not by itself supply:

- the repository's required orientation as a named trivial quotient rather than
  only a reducibility or nonirreducibility conclusion;
- the same result over every finite coefficient field of characteristic 3;
- a theorem for an `e_2 = 9` cyclic-inertia branch; or
- the subsequent characteristic-zero 3-adic Frobenius trace formula.

Those remain separate source and Lean obligations.

## Lean-oriented decomposition

The source evidence supports the following bounded design order without asserting
that the corresponding declarations already exist:

1. formalize the root-discriminant upper-bound input and the exact three Diaz y
   Diaz table constants as finite historical data;
2. prove the totally-imaginary and even-degree adapters from containment of
   `Q(zeta_3)`;
3. formalize Joshi's finite group case split to obtain nonirreducibility over
   `F_3`;
4. separately bridge the repository's `IsHardlyRamified` fields to Joshi's three
   printed hypotheses;
5. separately prove coefficient-field generalization and select the exact trivial
   quotient orientation consumed by `mod_three`; and
6. keep the all-powers-of-3 lift and Frobenius trace result outside this provider.

For Tate uniformization, the bounded design order is:

1. restrict or bridge the local-form boundary to a p-adic field;
2. instantiate Silverman V.5.3 to obtain the base-field Tate curve from split
   multiplicative reduction and nonintegral `j`;
3. combine that local form with the independently constructed explicit Tate
   uniformization; and
4. retain finite-flat torsion and Weil pairing as independent providers.

No step may be promoted on citation alone. Provider work still requires an exact
Lean hypothesis map, a discriminating consumer and negative probe, targeted and
full builds, declaration-level axiom output, and independent source-fidelity
review.
