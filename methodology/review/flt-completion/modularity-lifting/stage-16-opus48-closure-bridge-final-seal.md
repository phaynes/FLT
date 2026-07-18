# Opus 4.8 final build seal — closure-to-class absolute irreducibility

Verdict: **PASS-FINAL-SEAL**.

The reviewer pinned HEAD at `25b832064a1ea1...`, made no repository changes, and independently ran:

```text
lake build FLTMethodology.Probes.ResidualAbsoluteVocabulary
  -> Build completed successfully (3479 jobs)

lake build FLTMethodology
  -> Build completed successfully (9032 jobs)
```

An external Lean audit confirmed that each of:

- `adjoinRange_eq_top_of_isAlgClosed_irreducible`;
- `adjoinRange_eq_top_of_baseChange_eq_top`;
- `closureImpliesClassAbsIrred`

depends exactly on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axiom,
`knownin1980s`, `admit`, `unsafe`, or `native_decide` reaches the declarations.

The hostile mathematical check accepted the algebraically-closed density step, tensor-range
orientation, surjectivity and finrank descent, nontriviality of all scalar extensions, universe
pinning, and the definitional conversion to the repository class.

This seal authorizes promotion of `FLT-ABSIRRED-VOCAB` only. The concrete cyclotomic residual-image
providers and the Taylor source theorem remain open consumers.
