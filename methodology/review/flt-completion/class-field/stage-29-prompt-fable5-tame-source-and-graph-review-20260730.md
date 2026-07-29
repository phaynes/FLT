# Independent source and graph review — FLT tame residue

Review the post-kernel source-assurance and graph delta read-only.

- repository: `/Volumes/second-store/devel/proof-forks/FLT-tame-residue-completion-20260730`
- kernel candidate: `b78328972fb5d2072fb9959c7afcda0ff88e17b0`
- source/control candidate: `270a79f4e5f01340f2838a6ef8577f14afdfdd21`
- obligation: `FLT-TAME-RESIDUE`

You already independently passed the kernel candidate in Claude session
`69c8bf59-ed07-4c0c-a25c-53a549f849c8`. This is a distinct delta-only adjudication: do not repeat
the full proof review unless the source/control delta invalidates it.

## Evidence to inspect

- `methodology/evidence/sources/FLT-TAME-RESIDUE-NEUKIRCH-SOURCE-20260730.md`
- the `SRC-026` row in `methodology/SOURCE-REGISTER.md`
- `methodology/evidence/probes/FLT-TAME-RESIDUE-COMPLETION-20260730.md`
- the `FLT-TAME-RESIDUE` row and its four direct consumers in
  `methodology/control/proof-obligations.ndjson`
- `methodology/control/source-design.ndjson`
- `methodology/control/flt-completion-execution.ndjson`
- generated `methodology/control/proof-graph.ndjson`
- generated `methodology/spec/flt-proof-program.instances.json`
- the Stage 28 review response and attempt row

The exact inspected PDF remains available for this review at:

`/tmp/flt-neukirch-verify.BblY9u/neukirch.pdf`

Expected SHA-256:

`3f1516369f11c5786275d60b9130ee29b9bb0199fb345062055d60b50a715245`

Publisher record:

`https://link.springer.com/book/10.1007/978-3-662-03983-0`

University-hosted inspected scan:

`https://www.math.toronto.edu/~ila/Neukirch_Algebraic_number_theory.pdf`

## Required checks

1. Verify Git cleanliness, candidate ancestry, and that the post-kernel delta contains no Lean
   source changes.
2. Recompute the PDF SHA-256 and verify its page count/identity.
3. Render and visually inspect PDF pages 132, 166, and 185. Confirm the printed page numbers and
   exact propositions II.(3.8), II.(7.5), and II.(9.11).
4. Check that the packet paraphrases those propositions accurately and maps them only to facts they
   actually support.
5. Decide whether `SRC-026` is an exact authoritative source locator for this obligation. Keep the
   distinction between an authoritative monograph and an original research paper explicit.
6. Check that no local/global reciprocity, class-field package, cyclic base change, or FLT conclusion
   is laundered through this source.
7. Check the current state `kernel-complete-source-pending` and consumer caveat updates for schema,
   honesty, graph consistency, and non-closure of consumers.
8. Run `git diff --check 4642bcd..270a79f4e5f01340f2838a6ef8577f14afdfdd21`, parse every changed
   NDJSON file, run `python3 methodology/control/generate_graph.py`, and run
   `python3 methodology/control/flt_monitor.py`. Do not leave tracked files changed; restore only
   deterministic generator output if it is byte-identical, and otherwise report `REVISE` without
   modifying it.
9. State the exact post-review mutation, if any, that would be honest for:
   - `source_refs`;
   - `primary_source_exact`;
   - `current_state`;
   - `review_state` and `kernel_probe_state`;
   - the remaining completion gate.

## Verdict

Return exactly one leading verdict:

- `PASS-TAME-RESIDUE-SOURCE-GATE` if the three locators are visually exact, the mapping is bounded,
  and the source/control delta is honest;
- `REVISE` with the smallest exact defect;
- `NO-RESULT` only for an operational failure.

Do not edit, commit, push, or promote. Even on PASS, explicitly exclude `FLT-CLASS-FIELD`, all four
consumer closures, any T2 assumption authorization, and FLT.
