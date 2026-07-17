# Stage 3 prompt — Fable 5 Hecke-action diversity repair

Difficulty 10. This is the single serialized diversity-design pass triggered by the typed policy.
Act read-only. Do not edit the repository, graph, task state, source register, or Lean files.

Read:

- `methodology/review/flt-completion/hecke-action/stage-1-opus48-primary.md`;
- `methodology/review/flt-completion/hecke-action/stage-2-gpt56xhigh-review.md`;
- the exact `FLT-HECKE-ACTION`, `FLT-AUT-GALOIS`, `FLT-DEF-FUNCTOR`, `FLT-SGOOD-SELECTED`,
  `FLT-TW-PRIMES`, and `FLT-PATCHING` rows and edges;
- the live Hecke, automorphy, deformation, localization, and `R = T` APIs cited by those reviews.

Produce an independent repair design, not a commentary rephrasing. Hostilely test:

1. whether the GPT split between a Hecke-valued pseudorepresentation/determinant,
   residual-absolute-irreducibility, reconstruction, and a genuine `T₀`-valued representation is
   mathematically necessary and source-faithful;
2. whether any existing pinned theorem or exact registered source can remove or combine those nodes;
3. the smallest correct complete-local-Hecke-factor predicate, including coefficient-residue
   ownership, finiteness, topology, compactness, adic completeness, and the localization-to-factor
   construction;
4. whether the accepted U1 module, finite-over-Hecke instance, local base change, generic
   classifying map, `RToTActionData`, and T/U generator criterion are minimal and elaborate at the
   current pin;
5. the exact source and dependency owner for every missing theorem—especially local-factor
   existence, pseudorepresentation construction, reconstruction, deformation-point membership,
   multiplicity one, U-operator compatibility, and the patching adapter;
6. arithmetic/geometric Frobenius, determinant, nebentypus, coefficient-change, and level
   normalization against `GaloisRep.IsAutomorphicOfLevel`;
7. whether all nonzero `U_{v,α}` images are genuinely required for surjectivity or whether a smaller
   source-backed generator family suffices;
8. whether `FLT-DEF-FUNCTOR → FLT-HECKE-ACTION` and the proposed intermediate nodes give the
   transitively reduced orientation without reversing the patching dependency;
9. counterexamples to any attempted direct construction of `T₀`-valued `GaloisRep`, any claim that
   `Localization.AtPrime` is already a complete finite local factor, and any T-only surjectivity
   claim;
10. the first landable kernel-clean unit, the first genuine mathematical theorem after it, and the
    first expected Lean residual.

Run temporary Lean probes outside the repository for every accepted signature. Return exactly one
of `DESIGN-VIABLE`, `REVISE`, `UNCERTAIN`, or `REFUTED`, with exact signatures, dependency order,
source gates, probe results, standard-axiom audits, and stop-loss conditions. Do not propose public
axioms or generic `Prop` placeholders, and do not promote an interface merely because it elaborates.
