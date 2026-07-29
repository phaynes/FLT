# Stage 28 — Fable 5 independent executable review

## Verdict

`PASS-TAME-RESIDUE-KERNEL`

Fable independently accepted the exact theorem `localTameAbelianInertiaGroup_eq_ker` as
mathematically sound, freshly elaborated and rebuilt, and standard-trio clean.

## Independent execution

- candidate commit: `b78328972fb5d2072fb9959c7afcda0ff88e17b0`
- reviewer: `fable5-tame-completion-reviewer`
- model: `claude-fable-5`
- session: `69c8bf59-ed07-4c0c-a25c-53a549f849c8`
- transcript: `/Users/philiphaynes/.claude/projects/-Volumes-second-store-devel-proof-forks-FLT-tame-residue-completion-20260730/69c8bf59-ed07-4c0c-a25c-53a549f849c8.jsonl`
- model duration: `768,387 ms`
- bridge duration: `773,255 ms`
- turns: `41`
- input tokens: `29`
- cache creation input tokens: `158,562`
- cache read input tokens: `1,533,542`
- output tokens: `59,279`
- reported cost: `$7.669022`

The reviewer verified that the candidate is an ancestor of the review HEAD and that the post-freeze
delta consisted only of the Stage 28 prompt and configuration.

The reviewer independently ran:

- direct Lean elaboration of the 532-line provider: exit 0, zero diagnostics;
- direct Lean elaboration of the dedicated probe: exit 0;
- 34/34 new declaration axiom audits: exactly
  `[propext, Classical.choice, Quot.sound]`;
- 42/42 existing tame-boundary declaration audits: the same standard trio;
- targeted builds: 3,454 and 3,443 jobs, exit 0;
- full `FLT FLTMethodology` build: 9,047 jobs, exit 0;
- prohibited-token and hidden-provider checks: no tranche defect.

## Mathematical adjudication

Fable explicitly accepted:

1. local-inertia normality and the infinite Galois fixed-field step;
2. the finite integral-closure DVR, fraction-ring, and Galois instances as non-circular;
3. both directions of finite/infinite inertia restriction;
4. the actual-carrier use of `stabilizerHom_surjective_of_profinite`, the quotient action over the
   finite residue field, and the correction `sigma * rho^-1`;
5. trivial finite inertia implying ramification index one;
6. maximal-ideal generation, irreducibility, z-power/unit factorization, and coercions;
7. finite Galois containment of each fixed-field element;
8. exact satisfaction of the unchanged provider Prop and unconditional kernel theorem;
9. import direction and unchanged consumers;
10. consistency with the retained Neukirch locator review, without treating that citation as local
    primary-source verification.

The counterexample hunt included the `q = 2` edge case, a local value-group sanity check, and
instance/coercion ambiguity. No mathematical defect was found.

## Evidence-hygiene finding

`git diff --check 4642bcd..b783289` initially exited 2 because this controller evidence packet used
three Markdown two-space hard breaks. Fable correctly identified the packet's claim that the range
check passed as inaccurate. This is a documentation-only finding; the spaces were removed and the
claim was clarified after review. No Lean file changed.

## Promotion boundary

- kernel theorem, builds, and independent review: **passed**;
- source-grounded status: **not established** because no hash-verified local primary-source copy or
  `SRC-026` is present;
- honest obligation state: U1–U6 kernel-complete and independently reviewed, still source-assurance
  pending under the existing completion gate;
- downstream effect: the canonical tame-kernel semantics are available to the four registered
  consumers, but none of those consumers is thereby closed;
- excluded: `FLT-CLASS-FIELD`, any T2 assumption, the downstream consumer obligations, and FLT.

No graph mutation was performed by Fable.
