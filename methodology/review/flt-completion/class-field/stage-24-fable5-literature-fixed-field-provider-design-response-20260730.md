# Stage 24 — Fable 5 literature-grounded fixed-field provider design

## Run identity

- Model/profile: `claude-fable-5`, high effort, `fable5-designer-d8`
- Mode: read-only fresh session
- Exit: `0`
- Duration: `1,385,998 ms`
- Usage: input `123`, cache creation input `1,017,201`, cache read input `7,683,291`, output
  `344,938` across `66` assistant messages. Claude usage fields are reported separately and are not
  collapsed into the OpenAI token schema.
- Session: `7128a612-5bf5-42b6-adcd-6f0493bc886e`
- Exact transcript:
  `/Users/philiphaynes/.claude/projects/-Volumes-second-store-devel-proof-forks-FLT-tame-residue-completion-20260730/7128a612-5bf5-42b6-adcd-6f0493bc886e.jsonl`
- Transcript SHA-256: `eeb060cbd1411abf4ece81e0c9cfa1a2597576b2d2153b7cdbb7e56e1fc9875b`
- Full design plan:
  `/Users/philiphaynes/.claude/plans/literature-grounded-design-structured-hearth.md`
- Plan SHA-256: `706a52a39e79e75d224ae00da8e30b607d946241adc2eb8ad70b4fd03eb75005`
- Prompt SHA-256: `94a1b801decdb0cd90fc075dfcce0c42479ba6c4a5208849c5c125c261fb0d4e`

## Verdict

`IMPLEMENTABLE-NOW`.

Fable independently recovered the same finite-Galois/DVR route, then supplied a concrete candidate
for the exact reverse-inclusion bridge isolated by Stage 23. Given a finite inertia automorphism:

1. lift it arbitrarily to the absolute Galois group;
2. regard that lift's action on the infinite integral-closure residue field;
3. use `Ideal.Quotient.stabilizerHom_surjective_of_profinite` for the subgroup fixing the finite
   field to obtain a correcting automorphism with the same residue action;
4. multiply by its inverse, obtaining an infinite-inertia element with the required finite
   restriction.

The remaining construction is finite and ideal-theoretic: identify the inertia-fixed finite field,
use `card_inertia_eq_ramificationIdxIn` and the ramification tower to obtain index one, transfer the
base uniformizer to the finite DVR, factor the element as a uniformizer power times a unit, and map
the resulting unit into the algebraic closure.

The source-to-Lean translation was revalidated against Neukirch II.3.8, II.7.5 and II.9.11 using
the retained independent locator review. The worktree still lacks a local hash-verified SRC-026
copy/register entry; that is a source-assurance gap, not permission to invent a theorem or assume
the provider.

The full dependency graph, proposed signatures, counterexample audit, bounded slices, and stop-loss
rules are retained in the exact plan and transcript identified above. No repository source was
edited by the designer.
