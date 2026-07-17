# Stage 4 prompt — Opus 4.8 bounded build review for Moret--Bailly adapters

Difficulty 10; review budget 2100s. Work read-only. Do not edit repository files, task state,
control rows, or Lean sources. Temporary probes outside the repository are allowed.

Review only these newly persisted bounded units:

- `FLTMethodology/Probes/MoretBaillyFieldAdapters.lean`;
- `FLTMethodology/Probes/MoretBaillyLocalPointsAlgebraic.lean`;
- the corresponding imports in `FLTMethodology.lean`;
- the Moret--Bailly Stage-3 GPT review and current control rows.

Run the targeted Lake builds and independently audit:

- `FLT.PotentialModularity.linearDisjoint_of_compositum`;
- `AlgebraicGeometry.Scheme.ptsOver`;
- `FLT.PotentialModularity.MoretBailly.ptsMap`.

PASS only if the exact axiom surface is `[propext, Classical.choice, Quot.sound]`, the maps have the
claimed variance and base compatibility, and the control plane does not misdescribe these adapters
as a topology, source theorem, T2 boundary, or proof of `FLT-MORET-BAILLY`.

Return `PASS`, `REVISE`, `REFUTED`, or `NO VERDICT`, with exact residual goals. This review cannot
authorize an axiom, change `HIST-UNRESOLVED`, or promote the obligation from `absent`.
