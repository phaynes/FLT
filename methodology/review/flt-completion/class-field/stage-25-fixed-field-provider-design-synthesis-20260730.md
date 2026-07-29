# Stage 25 — fixed-field provider design synthesis

## Decision

Proceed with one GPT-5.6 xhigh proof-mutating builder, in four compiler-gated slices, using the
intersection of the two independent designs.

The two designs agree on the exact target, finite Galois reduction, ramification-index-one finish,
DVR factorization, statement validity, and the prohibition on replacing the provider with an
assumption. Their only apparent disagreement is resolved as follows:

- Stage 23 correctly isolates finite-inertia-to-infinite-inertia lifting as the only missing
  direction not supplied by plain Galois restriction surjectivity.
- Stage 24 proposes an implementation of precisely that direction using the pinned profinite
  residue-action surjectivity theorem.
- The builder must test this correction proof first. It may not treat Stage 24's existence claim as
  evidence until Lean accepts it.

## Ordered implementation

1. **Finite ring pack.** Port the already reviewed normality fact only if useful; construct the
   integral-closure map, finite/local/Dedekind/DVR instances, fraction-ring and maximal-ideal
   contraction facts required downstream.
2. **Restriction equality.** Prove the easy image inclusion. Prove the reverse inclusion by the
   profinite correcting-automorphism construction. Stop and report the exact failing carrier or
   instance if this cannot be made kernel-clean; do not assume it.
3. **Ramification and DVR factorization.** For a finite Galois subfield lying in the inertia fixed
   field, deduce trivial finite inertia, ramification index one, maximal-ideal equality, and
   uniformizer-power/unit factorization.
4. **Consumer closure.** Prove `fixedFieldUniformizerDecomposition` and the unconditional
   `localTameAbelianInertiaGroup_eq_ker`, without changing existing theorem statements.

Each slice must compile before the next. The final candidate requires the targeted module/probe
build, the existing tame-boundary regression build, the full `FLT FLTMethodology` build, exact
declaration-level axiom output, prohibited-token scan, independent review, and an honest graph
update. Only one agent may modify Lean proof state during this cycle.

## Authority and stop rules

- Lean is the mathematical oracle; model verdicts are designs only.
- No `sorry`, `admit`, `native_decide`, custom axiom, historical assumption, or renamed restatement
  of `FixedFieldUniformizerDecomposition` is allowed.
- Do not weaken hypotheses or alter the existing provider/consumer signatures.
- Keep the missing SRC-026 local-copy/register issue visible. Code may progress, but source-grounded
  promotion must remain distinct until the source evidence is current.
- If the profinite correction cannot instantiate at the actual carriers in one bounded cycle,
  return `IMPLEMENTABLE-AFTER-NAMED-LIBRARY-BRIDGE` with the smallest exact missing theorem.
