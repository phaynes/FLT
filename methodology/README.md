# Independent FLT proof-methodology experiment

This directory contains an independent proof-engineering experiment based on the public
Imperial College London FLT repository. It is not affiliated with, sponsored by, or endorsed by
Imperial College London or the upstream FLT project. Upstream authorship, copyright notices, and
the Apache-2.0 licence remain authoritative.

The experiment separates three completion targets:

- **T1 — sorry-free modulo 1980s:** the exported theorem has no `sorryAx`; the upstream
  `knownin1980s` boundary remains explicit.
- **T2 — finite historical-assumption interface:** the generic `knownin1980s` axiom is replaced by
  a finite, typed, source-linked list of assumptions. This is not an unconditional proof.
- **T3 — unconditional kernel-clean FLT:** the exported theorem depends only on `propext`,
  `Classical.choice`, and `Quot.sound`.

Scaffold modules under `FLTMethodology/` are design probes. They are deliberately outside the
verified `FLT` module root and are not proof progress. Only declaration-level axiom audits and the
fail-closed monitor can promote a graph node to kernel-clean.

The 2026-07-19 primary-literature review intake is recorded in
`evidence/sources/primary-literature-review-intake-20260719.md`, with a machine-readable
non-promoting delta in `control/literature-assurance-delta-20260719.ndjson` and bounded
Lean-construction aids in
`source-design/literature-assisted-proof-design-20260719.md`. These artefacts correct several
source identities and locators but do not change any proof-obligation or source-design status.
