INDEPENDENT STAGE-1 DESIGN — TATE-FREY REMAINING CLUSTER

Repository: /Volumes/second-store/devel/proof-forks/FLT
Baseline: branch methodology/varro-proof-program-20260716, start SHA 827eb96.

Act read-only. `FLT-TATE-TORSION` and `FLT-TORSION-001` are already integrated and audit to the
standard axiom trio; preserve them as regressions. Design only the remaining obligations
`FLT-TATE-FLAT`, `FLT-TATE-UNRAMIFIED`, `FLT-TATE-WEIL`, `FLT-SUPPORT-TATE`, and `FLT-FREY-HR`.
Inspect the exact consumer slice, `Flat.lean`, `GoodReduction.lean`, `TateCurve.lean`,
`WeilPairing.lean`, `HardlyRamified/Frey.lean`, existing probes/evidence, and the retained AINTLIB
slice. Do not accept the zero pairing or confuse unramifiedness with finite flatness.

Return: exact field-by-field `IsHardlyRamified` dependency graph; per-obligation source boundary;
minimal Lean signatures in build order; shared abstractions; library matches; statement-level
obstructions; counterexamples; parallel slices and join gate; first kernel-clean tranche; DoR
checklist; and `DESIGN-VIABLE`, `REPAIR-FIRST`, or `OBSTRUCTION`. Do not edit files.
