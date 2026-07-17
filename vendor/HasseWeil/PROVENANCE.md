# HasseWeil torsion-cardinality dependency slice

This directory retains the exact source dependency closure needed by
`HasseWeil.HasseBound.WeilPairing.TorsionCardEll`.

- Upstream repository: <https://github.com/CBirkbeck/AINTLIB>
- Upstream commit: `b91f668cd447754b83880f353c34e4a1ed236f2c`
- Retained closure: 52 Lean modules, selected from the successful `.olean` dependency closure of
  the target under FLT's pinned Lean 4.32.0-rc1 and Mathlib
  `a3364faec42918fcd84a03a255b50570129f9ead`.
- License: Apache 2.0, as stated in the retained source headers. `LICENSE` contains the license text.

## Mechanical compatibility transformation

The upstream sources predate Lean's enforced module visibility in this toolchain. The retained
copy therefore adds `module`, changes imports to `public import`, exposes the module section, and
promotes internal helper declarations where a downstream module consumes them. These changes alter
visibility and packaging, not theorem statements.

Two upstream admissions were removed from the retained dependency closure after a consumer search
showed that the declarations were obsolete and unused by the target:

- the Wronskian theorem chain formerly admitted in `Foundation/OmegaPullbackCoeff.lean`;
- the bridge theorem formerly admitted in `Isogeny/FormalSeries.lean`.

The target slice contains no executable `sorry`, `admit`, custom `axiom`, `unsafe`, or
`native_decide`. The retained capstone and the FLT provider are audited by Lean to depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Retained modules

The source manifest is `MODULES.txt`. Regenerate the dependency selection only from a successful
target build and review any change to that manifest as a dependency change.
