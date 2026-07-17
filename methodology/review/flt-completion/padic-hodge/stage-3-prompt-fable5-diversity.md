CONDITIONAL FABLE 5 DIVERSITY DESIGN — P-ADIC HODGE REPAIR

Act as the independent Fable diversity designer for `FLT-MLT-PADIC-HODGE` at difficulty 10. Work
read-only. Read:

- `methodology/review/flt-completion/padic-hodge/stage-1-opus48-primary.md`
- `methodology/review/flt-completion/padic-hodge/stage-2-gpt56xhigh-review.md`
- `methodology/review/flt-completion/coefficients/stage-3-fable5-diversity.md`
- `methodology/MLT-SOURCE-CONTRACT.md`
- the current coefficient, integral-model, local-Galois, number-field, and ramification APIs.

The mandatory GPT review found substantive statement-level defects. Do not patch them cosmetically.
Produce an independent repaired design that:

1. Gives an exact elaborating `AbstractWeightLocalData`-style signature using global embeddings
   `F →+* AlgebraicClosure ℚ_[ell]`, the exact `[a, a + ell - 2]` source interval, and
   `Algebra.IsUnramifiedIn`.
2. Keeps `IsCrystallineAt`, Hodge–Tate weight extraction, and the finite-flat-to-crystalline theorem
   as explicit definition/theorem gaps rather than placeholder propositions or citations.
3. Separates the integral representation `rho0` from its characteristic-zero generic fibre `rho`,
   exposes scalar-extension equivalence and compatibility, and states the bridge conclusion at the
   correct representation.
4. Resolves, or precisely isolates, the dual/sign convention between Taylor's cyclotomic weight
   `-1`, the use of etale H1 as a dual Tate module, and the repository's cyclotomic determinant.
5. Keeps automorphic `π_v` unramifiedness in the RACAR/source boundary, with the required dependency
   edge, rather than encoding it in a Galois-side shortcut.
6. Distinguishes definitions/probes buildable now from genuine p-adic-Hodge T1 mathematics, with
   exact owners and a dependency-ordered graph.
7. Identifies the smallest next Lean probe and tests important signatures in temporary files.

Preserve the frozen T1 axiom policy: no `sorry`, generic authority, T2 deferral, or promotion. Return
`DESIGN-VIABLE`, `DECOMPOSE-FIRST`, or `OBSTRUCTION`. Do not edit repository files or register an
axiom.
