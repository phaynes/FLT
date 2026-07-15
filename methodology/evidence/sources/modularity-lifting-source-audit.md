# Modularity-lifting source audit

This note records source conditions; it does not select or prove a Lean theorem.

## Blueprint temporary target

The frozen blueprint asks for a weight-two modularity-lifting theorem over an even-degree totally
real field in which the residual prime is unramified. Its temporary `S`-good condition fixes the
determinant, ramification set, tame trace condition, and flatness at primes above the residual
prime. The blueprint itself says it is far from stating this result in Lean and does not identify an
exact literature theorem.

## Taylor, Theorem 3.3

Taylor's theorem assumes, among other conditions:

- a prime greater than three;
- a totally real even-degree field in which that prime splits completely;
- a continuous irreducible representation that is crystalline at every place above the prime with
  Hodge-Tate numbers in the stated range;
- residual irreducibility after restriction to the specified cyclotomic quadratic extension; and
- a residual automorphic representation with the stated unramified finite components and weight.

It concludes automorphy of the lift. This is not the blueprint contract verbatim. A possible route
is to make the auxiliary field satisfy the stronger split-completely condition and prove all other
hypotheses, but that route requires its own source-compatible case split and Lean contracts.

## Gee, Theorem 5.2

Gee's theorem compares two congruent representations. It allows the prime to be unramified in the
totally real field and assumes matching distinct bounded Hodge-Tate weights and crystalline local
representations. It additionally assumes residual image containing `SL₂(F_p)`. That image condition
does not follow merely from irreducibility of an arbitrary hardly-ramified residual representation.

## Design consequence

Neither near-reference can be lowered unchanged into the blueprint's temporary theorem. Before
`FLT-SGOOD-DEF` or `FLT-MLT` is signature-frozen, review must choose one of:

1. Taylor plus a stronger constructed auxiliary field and a separately sourced treatment of the
   residual representations failing the cyclotomic irreducibility condition;
2. Gee plus a proof that every representation reaching the theorem has the required large image;
3. another exact primary theorem; or
4. an explicit chain of sourced bridge theorems deriving the desired contract.

No generic authority axiom or assumed bridge is an acceptable repair.
