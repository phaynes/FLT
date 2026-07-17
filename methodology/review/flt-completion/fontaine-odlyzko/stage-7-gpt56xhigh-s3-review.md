PASS

- The unchanged probe compiles; all 13 declarations audit exactly `[propext, Classical.choice, Quot.sound]`, with no Fontaine–Odlyzko assumptions or admitted results.
- Rank two establishes `Nontrivial V` before irreducibility is unfolded, excluding the zero-space counterexample. The resulting stable `W` is nonzero, proper, and both `W` and `V ⧸ W` have finrank one.
- Quotient equivariance has the correct orientation: `mkQ (ρ g v) = quotientRepresentation g (mkQ v)`.
- `quotientEquiv` is explicitly chosen. `quotientCharacter := LinearMap.det.comp quotientRepresentation` is independent of that coordinate; its dependence on the selected stable line is correctly exposed through `D`.
- No triviality is inferred. For example, a reducible diagonal `1 ⊕ ψ` can yield quotient character `ψ`, depending on the selected line.

Smallest production slice: Opus declarations 1–3—`exists_proper_invariant_submodule`, `finrank_split_of_proper`, and `s3_reducibility_bridge`. In the controller’s packaged form, this is `ReducibleRankTwoData`, `exists_reducibleRankTwoData`, `quotientRepresentation`, `quotient_surjective`, and `quotient_equivariant`.

First residual mathematical goal: use the hardly-ramified local/global input to select and orient a stable line whose quotient character is trivial. It is not valid to prove triviality for an arbitrary `D` returned by reducibility alone. The full Fontaine–Odlyzko obligation remains open.
