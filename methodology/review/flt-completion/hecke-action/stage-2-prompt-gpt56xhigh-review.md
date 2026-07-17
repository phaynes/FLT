# Stage 2 prompt — GPT-5.6 xhigh independent Hecke-action review

Difficulty 10. Fresh independent read-only review. Do not edit the repository, graph, source
register, Lean files, task state, or review artifacts.

Read:

- `methodology/review/flt-completion/hecke-action/stage-1-prompt-opus48-primary.md`
- `methodology/review/flt-completion/hecke-action/stage-1-opus48-primary.md`
- the exact obligation, graph, source-design, and source-register rows for `FLT-HECKE-ACTION`;
- the exact consumers in `FLT/Patching/REqualsT.lean` and the current Hecke algebra, automorphy,
  representation, localization, and deformation APIs cited by the design;
- the live designs for `FLT-SGOOD-SELECTED`, `FLT-AUT-GALOIS`, `FLT-DEF-FUNCTOR`,
  `FLT-TW-PRIMES`, and `FLT-PATCHING`.

Hostilely adjudicate the Opus `READY-FOR-GPT-REVIEW` design. In particular:

1. determine whether a genuine `T₀`-valued `GaloisRep` is justified at this boundary or whether the
   source/library surface only supports a pseudo-representation or determinant before an explicit
   reconstruction theorem;
2. verify localization at a maximal ideal, completeness/locality, module finiteness, coefficient
   ownership, and residue-characteristic hypotheses against the exact Lean pin;
3. check arithmetic-versus-geometric Frobenius, determinant normalization, nebentypus, and every
   trace field against `GaloisRep.IsAutomorphicOfLevel`;
4. check that surjectivity covers all required `T` and `U` generators and is not falsely inferred
   from the anemic Hecke algebra;
5. verify that the proposed `(RtoT, smul_compat)` projection really instantiates the exact
   `ker_RtoT_le_nilradical` interface and that no dependency edge is reversed;
6. separate definitions/data bundles that can land now from analytic attachment,
   multiplicity-one/freeness, deformation representability, and Taylor--Wiles generation theorems;
7. reject any public axiom proposed merely to make a T1 interface elaborate. Missing provider
   theorems must stay named graph obligations, not become hidden assumptions;
8. test the U1/U2 signatures and every asserted existing instance with temporary Lean probes;
9. give the smallest accepted public surface and transitively reduced dependencies;
10. identify the first buildable kernel-clean unit and the first genuine mathematical theorem after
    it.

Apply the typed diversity rule exactly. Return one of `PASS`, `REVISE`, `UNCERTAIN`, or `REFUTED`.
If not PASS, classify the defects as either:

- `SUBSTANTIVE-MATHEMATICAL-OR-STATEMENT-LEVEL`, which triggers the conditional Fable pass because
  this component has difficulty 10; or
- `MECHANICAL-OR-SCOPE-ONLY`, which does not trigger Fable.

Give exact accepted Lean signatures, source/gate ownership, dependency orientation, temporary-probe
results, and the first expected Lean residual. No promotion is authorized by the review itself.
