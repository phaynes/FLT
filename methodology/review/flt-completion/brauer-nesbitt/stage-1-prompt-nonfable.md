# Independent Stage-1 design: `brauer-nesbitt` / `FLT-BRAUER-NESBITT`

Repository: `/Volumes/second-store/devel/proof-forks/FLT`  
Frozen design baseline: branch `methodology/varro-proof-program-20260716`, SHA
`827eb969aff49fb5c5a1b17f807426d3be1b4056`  
Pipeline: `tri-design-synthesis-build`, stage 1, independent read-only design  
Disposition: produce  
Target stage: T2 and ultimately T3 standard-axiom closure.

Act as an independent source-faithful mathematical and Lean architect. Read the repository, but do
not edit it or create files. Do not use another model's design. This is a fresh one-shot design.

The unchanged production contract is `FLT.Components.BrauerNesbitt.Contract`: finite-dimensional
semisimple representations over an arbitrary field and arbitrary group, equality of characteristic
polynomials for every group element, and equivalence of representations. The repository already
has a kernel-clean finite joint-image reduction to `FiniteJointImageContract`, trace extraction,
product-module transport, a rank-two odd-characteristic residual specialization, and a finite
regression refuting a trace-only weakening in characteristic two. The terminal theorem is absent.
The documented separable splitting-field route is incomplete over imperfect fields. The residual
consumer and characteristic-zero compatible-family/Chebotarev consumer are genuinely different;
almost-all Frobenius equality is not the current all-group-elements hypothesis.

Inspect at least:

- `FLT/Components/Contracts/BrauerNesbitt.lean` and its exact consumers;
- `FLTMethodology/Probes/BrauerNesbittBoundary.lean` and
  `FLTMethodology/Probes/MLTSourceBoundary.lean`;
- `methodology/source-design/brauer-nesbitt.md`,
  `methodology/evidence/probes/FLT-BRAUER-NESBITT.md`, the Fable/GPT boundary reviews, and the
  contract audit;
- the `FLT-BRAUER-NESBITT`, `FLT-MLT-COEFFICIENTS`, `FLT-CHEBOTAREV`, and
  `FLT-COMPAT-CONTRA` graph rows;
- pinned Mathlib semisimple-module, Jacobson-radical, simple/isotypic component, central simple
  algebra, scalar-extension/descent, character, and representation-equivalence APIs;
- `SRC-018` and `SRC-019`, preserving the primary-versus-secondary source distinction.

Return one implementable report with these exact sections:

1. **Observed baseline and consumers.** Give exact current declarations/types, proved reductions,
   actual consumers, and graph-only consumers, with file references. Say which coefficient regime
   and equality hypothesis each consumer really has.
2. **Source theorem boundary.** Identify exact source statements and locators. Decide whether the
   unchanged arbitrary-field theorem has an adequate source route, or whether two exact
   consumer-specialized terminals are the safer contract. Do not upgrade the 1937 paper or Wiese's
   notes beyond what they establish.
3. **Architecture choice.** Propose either (a) a valid imperfect-field-safe proof of the unchanged
   umbrella, or (b) two exact residual/characteristic-zero theorems that discharge every live
   consumer without weakening public conclusions. Explain why the choice is complete.
4. **Exact Lean signatures in dependency order.** Give full Lean syntax for every missing lemma,
   including namespaces, universes, assumptions, and conclusions. Label dependencies
   `EXISTING-PROVED`, `EXISTING-ADMITTED`, or `PROPOSED`. The first signature must attach directly to
   a current kernel-clean reduction or consumer.
5. **Pinned-library matches.** Give exact checked declaration names/types and classify each as exact,
   adaptable, or insufficient. Identify the first genuinely absent algebra theorem.
6. **Counterexamples and statement risks.** Cover imperfect fields, trace-only positive-characteristic
   failure, characteristic-polynomial nonlinearity on group algebras, finite/infinite groups,
   semisimplicity transport, scalar-extension descent, characteristic-zero versus residual rank-two
   use, and the separate Chebotarev continuity bridge.
7. **Smallest buildable first slice.** Specify exact file/theorem scope, a bounded proof plan,
   targeted build/audit commands, and the first likely residual Lean goal. It must reduce the real
   terminal, not add another equivalent contract.
8. **Dependency graph and gates.** Give the local DAG, completion criterion, and explicit stop-loss
   tests for false statements, unavailable descent, or source mismatch.
9. **Verdict.** Return exactly one of `DESIGN-VIABLE`, `NARROWING-ONLY`, or `OBSTRUCTION`, followed
   by a concise reason and the next exact theorem/signature to attempt.

No proposed assumption may contain `Contract`, `FiniteJointImageContract`, representation
equivalence, or the desired consumer uniqueness as an unproved hypothesis. Lean kernel evidence,
not source familiarity, will be the eventual completion authority.

