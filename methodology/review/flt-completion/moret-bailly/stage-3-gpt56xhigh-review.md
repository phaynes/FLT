# GPT-5.6 xhigh independent review after Fable diversity — Moret--Bailly

Verdict: **REVISE** (substantive statement/source repair).

Session: `019f702f-496a-75c3-9c67-d7f4beea8d07`  
Mode: read-only independent comparison  
Repository edits by reviewer: none

## Adjudication

1. The proposed `N0`--`N2` tranche is not valid as a single frozen unit.
   `Scheme.ptsOver` and algebraic `ptsMap` elaborate, but the displayed affine-chart domain does
   not: an `X.Over (Spec K)` instance does not supply `Algebra K Γ(X,U)`. A proposed `ptsEquiv`
   also needs continuity of its inverse, not only its forward map.
2. The proposed `⨆ TopologicalSpace.coinduced ...` construction uses the correct order for
   Mathlib's reversed topology lattice. An initial objection to the infimum/supremum direction was
   withdrawn. The unresolved issue is instead agreement with the classical valuation topology;
   that comparison is part of the source-level meaning of `open` and cannot be deferred to T3.
3. The pinned libraries do not provide a generic v-adic topology on scheme-valued points. That is a
   genuine provider gap, not an import repair.
4. The Moret--Bailly 1989 source located by the review is II, Theorem 1.3, p. 182, with Remark 1.5:
   <https://www.numdam.org/item/10.24033/asens.1582.pdf>. It does not directly state that the
   resulting global field is Galois or linearly disjoint from an arbitrary avoidance field.
5. The stronger blueprint-shaped package is closer to Barnet-Lamb--Gee--Geraghty--Taylor,
   Proposition 3.1.1:
   <https://annals.math.princeton.edu/wp-content/uploads/annals-v179-n2-p03-p.pdf>. Selecting that
   later result would be an explicit modern derived boundary, not an exact reading of MB89.
6. Therefore `primary_source_exact` and `hypothesis_translation` must both remain false, and
   `HIST-UNRESOLVED` remains the only honest historical/source disposition. No axiom or provider
   node is promoted by this review.

## Ownership corrections

- Even degree is a project/Jacquet--Langlands adapter, not a direct MB89 conclusion.
- Galoisness and avoidance-field disjointness belong to a proved derivation or an explicitly
  selected later source.
- Good reduction belongs to `FLT-AUX-CURVE`.
- Field unramifiedness belongs to `FLT-AUX-LOCAL-FIELD`.
- Representation or witness unramifiedness belongs to `FLT-AUX-CURVE`.

## Kernel-clean bounded units

The review accepted two smaller units, subsequently persisted and built:

- `FLT.PotentialModularity.linearDisjoint_of_compositum`;
- `AlgebraicGeometry.Scheme.ptsOver` and
  `FLT.PotentialModularity.MoretBailly.ptsMap`.

Each audits to exactly `[propext, Classical.choice, Quot.sound]`. These are algebraic adapters only;
they do not establish the local-point topology or the Moret--Bailly existence theorem.

## Next gate

Choose and independently source-review one exact theorem contract:

1. MB89 Theorem 1.3 plus separately proved Galois/disjointness and project-condition adapters; or
2. the later Proposition 3.1.1 as an explicit modern derived boundary.

Before either can be frozen, build a canonical v-adic topology on `X.ptsOver K K_v` and prove its
agreement with the source's local topology. No T2 registration is authorized.
