# Independent review: rank-two Brauer–Nesbitt consumer wiring

Review commit `10023b2` read-only against parent `3dbc1e7`. Do not edit the
repository and do not trust the producer evidence prose.

The code change is intentionally small: it adds
`FLTMethodology.Taylor2018.Coefficients.latticeIndependent_rankTwo` and its
bundle form. Determine whether the existing `CoefficientData` hypotheses
really provide both rank-two facts, semisimplicity, and characteristic-
polynomial equality needed by
`FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two`.
Check that the resulting `Representation.Equiv` is converted into the exact
`SemisimpleResidualEquivalent` target, including the Galois intertwining law.

Run a fresh targeted build and declaration-level `#print axioms` audit. Also
run `lake build FLT FLTMethodology` if the read-only environment permits it.
Check for hidden `sorry`, `admit`, custom axioms, circular assumptions, and
vacuity. Treat the earlier proof review as context, not as authority for this
new consumer.

Return exactly one terminal verdict, `PASS` or `REVISE`, followed by numbered
findings with file and line references. A `PASS` closes only the encoded
rank-two coefficient/lattice Brauer–Nesbitt consumer. It must not be described
as closing Chebotarev, all coefficient providers, the general-dimensional
contract, or FLT.
