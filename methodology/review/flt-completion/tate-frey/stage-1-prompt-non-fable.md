INDEPENDENT STAGE-1 DESIGN — TATE-FREY REMAINING CLUSTER

Repository: `/Volumes/second-store/devel/proof-forks/FLT`
Branch: `methodology/varro-proof-program-20260716`
Work-order start SHA: `827eb96`
Pipeline: `tri-design-synthesis-build`, Stage 1 only

## Authority and scope

Act as an independent mathematical and Lean designer in a fresh one-shot context. Read the actual
repository but make no edits, create no files, run no mutating commands, and do not implement any
proof. Ignore all other Stage-1 model outputs so this design remains independent.

`FLT-TATE-TORSION` and `FLT-TORSION-001` are already integrated, full-build green, and audited to
`[propext, Classical.choice, Quot.sound]`. Preserve them as regressions; do not redesign, weaken, or
reopen them. Design only the remaining produced obligations:

- `FLT-TATE-FLAT`;
- `FLT-TATE-UNRAMIFIED`;
- `FLT-TATE-WEIL`;
- join-only `FLT-SUPPORT-TATE`;
- `FLT-FREY-HR`.

The design must expose independent sources for finite flatness at `P.p`, unramifiedness away from
`2 * P.p`, cyclotomic determinant, and the tame-at-two quotient. Do not confuse unramifiedness with
finite flatness. Do not accept the current zero-valued `weilPairing` inhabitant as source-faithful.

## Mandatory repository inspection

Inspect at least:

- the exact assigned rows in `methodology/control/proof-obligations.ndjson` and component
  `tate-frey` in `methodology/control/source-design.ndjson`;
- `methodology/source-design/tate-uniformization.md`;
- `methodology/evidence/probes/FLT-TATE-FLAT-CONSUMER-SLICE.md`,
  `FLT-TATE-UNRAMIFIED-DEPENDENCY-SLICE.md`, `FLT-TATE-WEIL-CONSUMER-SLICE.md`,
  `FLT-TATE-TORSION-AINTLIB-AUDIT.md`, and the other related kernel probes;
- `FLT/GaloisRepresentation/HardlyRamified/Defs.lean` and `Frey.lean`;
- `FLT/KnownIn1980s/EllipticCurves/Flat.lean`, `GoodReduction.lean`, `TateCurve.lean`,
  `WeilPairing.lean`, and their exact imports/consumers;
- the completed `FLT/EllipticCurve/Torsion*.lean` provider and downstream Galois representation
  only to preserve its exact regression boundary;
- `methodology/SOURCE-REGISTER.md`, especially `SRC-001`, `SRC-023`, and `SRC-024`;
- all actual pinned APIs for Tate series/evaluation, quotient groups, variable changes,
  reduction, inertia, finite flatness/group schemes/Hopf algebras, roots of unity, determinant,
  Weil pairing, and local/global Galois transport.

Locate and quote exact current declaration types and proof admissions. Use repository search and, if
useful, read-only temporary `#check` probes outside the repository. Do not treat a methodology probe
as a provider unless its exact assumptions are proved for the concrete Frey/Tate objects.

## Required design analysis

Provide all of the following:

1. Exact field-by-field decomposition of
   `GaloisRepresentation.IsHardlyRamified`: `det`, `isUnramified`, `isFlat`, and `isTameAtTwo`.
   Map every field to exact producer declarations, source locators, and assigned obligation owner.
2. For `FLT-TATE-UNRAMIFIED`, decompose the nine provider admissions through concrete local-field
   evaluation of Tate `X/Y`, addition/homomorphism, characteristic-two-safe surjectivity, exact
   kernel, quotient equivalence, local-form classification, base change, Galois compatibility, and
   separable-closure transport. Identify which existing probes are mechanical joins versus open
   mathematical providers.
3. For `FLT-TATE-FLAT`, keep separate: universal division-polynomial resultant identity;
   good-reduction specialization/inertia injectivity and local/global action transport; and the
   genuine finite-flat group-scheme/Hopf-algebra model at the residue characteristic. Test whether
   any can be avoided for the exact `Frey.lean` consumer rather than assuming all current scaffolding
   is necessary.
4. For `FLT-TATE-WEIL`, design a source-faithful nonzero/perfect alternating Galois-equivariant
   pairing construction and the exact Tate normalization needed by determinant. Show how the type
   excludes the existing zero-pairing counterexample and how its dependency on
   `tateEquivSepClosure` is staged.
5. Exact proposed Lean signatures in dependency order, with universes, typeclasses, fields,
   valuations, curves, torsion modules, representations, and transports sufficiently explicit for
   elaboration. Mark each as existing, probe-proved conditional, new produced lemma, or source gate.
6. A transitively reduced dependency graph showing independent parallel slices, the
   `FLT-SUPPORT-TATE` join, and final `FreyCurve.torsion_isHardlyRamified` assembly. Include regression
   edges to the already-closed torsion/Galois provider without putting them back in scope.
7. Exact pinned library matches for every leaf, or `NONE FOUND`. Do not infer a finite-flat group
   scheme or Weil pairing API from mathematical terminology alone.
8. Counterexamples and hostile checks: zero pairing; same `j` but nontrivial quadratic twist;
   characteristic-two arguments that divide by two; quotient map without exact kernel or
   surjectivity; good-reduction unramifiedness used as flatness at residue characteristic;
   algebraic-closure versus local separable-closure torsion; sign/functoriality mismatch;
   output/update of a local Galois action transported through the wrong base-change map; and any
   circular use of `torsion_isHardlyRamified`.
9. A first buildable kernel-clean tranche for each independent slice, plus the single best first
   tranche overall. Give exact module placement/imports, signature, existing inputs, expected first
   Lean residual goal, and audit command.
10. Stop-loss gates for false statements, unverified printed source scope, absent foundational APIs,
    and any route that would require an unapproved named assumption.
11. A Definition-of-Ready checklist per obligation and for the join.

## Output contract

Return exactly these sections:

1. `VERDICT` — one of `DESIGN-VIABLE`, `REPAIR-FIRST`, or `OBSTRUCTION`, with one paragraph.
2. `CURRENT EXACT BOUNDARY`
3. `FIELD-BY-FIELD CONSUMER AND SOURCE AUDIT`
4. `DEPENDENCY GRAPH AND PARALLEL SLICES`
5. `PROPOSED LEAN SIGNATURES`
6. `LIBRARY MATCHES`
7. `COUNTEREXAMPLES AND FAILURE MODES`
8. `FIRST BUILDABLE SLICES`
9. `STOP-LOSS GATES`
10. `DEFINITION OF READY`
11. `OPEN QUESTIONS FOR SYNTHESIS`

Be explicit about every unverified source condition and absent library object. A source citation,
conditional probe, scaffold, or `sorry` declaration is not a completed provider.
