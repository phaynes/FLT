# Independent review: rank-two Brauer--Nesbitt

Review the producer commit `7a6603ee7c1003dc95deb8074376cc5c09a1b60a` read-only against its parent
`80551f00ff4cb8697cf2db605f289c18f735382b`. Do not edit the repository. Do not trust the
producer's claims or prior review prose.

The bounded claim is not the arbitrary-dimensional `Contract`. It is the rank-two theorem
`FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two` over an arbitrary
field, together with `RankTwoContract`. The intended FLT effect is only that this theorem can serve
two-dimensional residual and characteristic-zero consumers once their separate semisimplicity,
rank-two, and all-group-element characteristic-polynomial premises are proved. Chebotarev and those
consumer premises are out of scope and remain open.

Independently inspect every changed Lean declaration. Pay particular attention to:

- whether the degree-two Amitsur step really extends characteristic-polynomial equality from the
  group image to every element of the joint-image algebra without a hidden field-cardinality,
  perfectness, algebraic-closure, or characteristic restriction;
- whether the Wedderburn--Artin reconstruction over possibly noncommutative division rings is
  mathematically valid, including the scalar towers, central-component decomposition, Morita
  equivalence, finite-dimensional transport, and conversion back through the algebra equivalence;
- whether equality of the characteristic polynomials of central idempotent actions really forces
  equality of every block multiplicity and hence an equivalence over the semisimple algebra;
- whether all local instance changes and transported module structures preserve the intended maps;
- whether the final module equivalence is genuinely a group-representation equivalence;
- whether the public statement is neither vacuous nor circular and does not assume any equivalent
  form of the target;
- exact axiom closure and any hidden `sorry`, `admit`, custom axiom, or unsafe declaration;
- whether importing the files from `FLT.lean` is appropriate and whether the change breaks the
  umbrella build.

Run your own targeted build and declaration-level `#print axioms` audit from this exact commit.
Distinguish kernel/build validity from mathematical scope and source assurance. Return exactly one
terminal verdict, `PASS` or `REVISE`, followed by numbered findings with file and line references.
A `PASS` means the bounded rank-two theorem is sound and suitable for integration; it must not be
worded as completion of arbitrary-dimensional Brauer--Nesbitt, Chebotarev, or FLT.
