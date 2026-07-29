# FLT tame-residue source assurance — Neukirch

Date: 2026-07-30

Obligation: `FLT-TAME-RESIDUE`

## Bibliographic identity

Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren der mathematischen Wissenschaften 322,
Springer, 1999.

- publisher record: `https://link.springer.com/book/10.1007/978-3-662-03983-0`
- DOI: `10.1007/978-3-662-03983-0`
- ISBN: `978-3-540-65399-8`
- inspected scan: `https://www.math.toronto.edu/~ila/Neukirch_Algebraic_number_theory.pdf`
- retrieved object size: `10,521,773` bytes
- retrieved object SHA-256:
  `3f1516369f11c5786275d60b9130ee29b9bb0199fb345062055d60b50a715245`
- PDF pages: `581`

The scan was used for inspection only and was not added to Git.

## Visual locator checks

The following scan pages were rendered to PNG at 200 dpi and inspected as page images, not accepted
from OCR alone.

| Book locator | Printed page | PDF page | Verified content and proof consumer |
|---|---:|---:|---|
| Chapter II, Proposition (3.8) | 120 | 132 | Characterizes the valuation ring, its unit group, and its unique maximal ideal by valuation. This supports the DVR/uniformizer and unit-factor interpretation used at finite levels. |
| Chapter II, Proposition (7.5) | 154 | 166 | Identifies the residue field and value group of the maximal unramified extension. This supports the claim that the inertia-fixed route is unramified and does not enlarge the value group. |
| Chapter II, Proposition (9.11) | 173 | 185 | Identifies the inertia field with the maximal unramified subextension; the following paragraph states the Henselian/separable-closure specialization and residue Galois correspondence. This is the direct source locator for the fixed field of local inertia. |

The page headers, proposition numbers, printed page numbers, and surrounding hypotheses were all
legible in the rendered images.

## Source-to-Lean mapping

The production proof does not import a source-shaped axiom. It formalizes the route through existing
Lean/Mathlib declarations:

1. `localInertiaGroup_normal` and `fixedField_localInertia_isGalois` establish the fixed-field
   Galois setting.
2. `map_localInertiaGroup_eq_finiteInertia` is the finite/infinite inertia bridge, with the hard
   direction implemented by the profinite residue-action correction.
3. `finiteInertia_eq_bot_of_le_fixedField` and
   `ramificationIdx_eq_one_of_le_fixedField` express the unramified consequence at finite level.
4. `map_maximalIdeal_eq_maximalIdeal_of_le_fixedField` and
   `exists_eq_tameUniformizerInteger_zpow_mul_integralUnit` express the unchanged value group and
   uniformizer/unit factorization.
5. `exists_finiteGaloisIntermediateField_le_fixedField` and
   `fixedFieldUniformizerDecomposition` assemble the infinite fixed-field statement.
6. `localTameAbelianInertiaGroup_eq_ker` applies the unchanged conditional kernel theorem.

## Scope and non-claims

- This source packet supports the local valuation, unramified-extension, and inertia-field facts
  used by the proof.
- It does not source local or global reciprocity, cyclic base change, potential modularity, or any
  other `FLT-CLASS-FIELD` field.
- It does not turn the citation into Lean evidence; the controller builds and declaration-level
  axiom audits remain the mathematical verification authority.
- The scan is an authoritative monograph copy hosted by a university. This packet does not claim it
  is an original research-paper source for every underlying classical theorem.

Independent review of this exact locator-to-Lean mapping is required before changing
`primary_source_exact` or closing the source gate.
