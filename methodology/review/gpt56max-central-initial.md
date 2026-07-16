# GPT-5.6 Max central hostile review

Review commit: `5d376d153ad1641113781c317ee9ab69d38f200b`

Model: `gpt-5.6-sol`; reasoning tier: `max`.

## Verdict as returned

**NO SOURCE-COMPLETE ROUTE among the two supplied candidates**

The review independently rejected Taylor 2006, Theorem 3.3 and Gee 2022, Theorem 5.2. It confirmed
the split-versus-unramified mismatch, the false large-image bridge for an induced residual seed,
the missing coefficient and GL2/quaternionic automorphy bridges, and the fact that
`ker_RtoT_le_nilradical` is not an `R = T` isomorphism.

The initial inspection gathered source and Lean evidence but timed out before a verdict. A fresh,
evidence-only synthesis completed in 137 seconds. The synthesis had not been supplied Taylor 2018,
Theorem 2.1.1, so its negative verdict does not adjudicate that theorem.

Kernel evidence reproduced:

- `GaloisRep.IsAutomorphicOfLevel`, `GaloisRep.charFrob`,
  `GaloisRepresentation.IsHardlyRamified`, and `ker_RtoT_le_nilradical` use only the standard axiom
  trio;
- `cyclic_base_change` and the relevant deformation/corepresentability declarations contain
  `sorryAx`;
- generic RACAR/automorphy, crystalline, and Hodge--Tate interfaces are absent.

New mathematical evidence: no surviving route beyond the supplied candidates; substantial
statement-level obstruction evidence for those candidates.
