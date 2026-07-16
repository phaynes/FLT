# Fable 5 review: Brauer--Nesbitt consumer narrowing

Candidate commit: `61ca825611de277f22289404f39ffac4df87b650`.

Model: `claude-fable-5`.

Execution: fresh, independent, read-only review; 481,975 ms. The reviewer received the immutable
public FLT snapshot and the specialized consumer bridge, but not the GPT report.

Verdict: **NARROWING PARTIAL ONLY**.

## Findings

- `specializedResidualModelsUnique` is a sound conditional bridge from the algebraically closed,
  rank-two, odd-characteristic trace theorem to the same-field residual-model consumer.
- No current live consumer establishes all of those hypotheses. The Taylor coefficient branch still
  lacks graph-proved algebraic closure, rank transport, and odd residual characteristic.
- The compatible-family members currently use `AlgebraicClosure ℚ_[p]`, which is characteristic
  zero. The residual odd-characteristic specialization therefore cannot discharge that terminal.
- The compatible-family interface supplies almost-all Frobenius comparison, not equality on every
  group element. A Chebotarev/continuity bridge and semisimplicity remain explicit obligations.
- A source-faithful split is possible only after separate residual and characteristic-zero
  comparison nodes, plus any necessary coefficient descent, receive exact interfaces.

## Gate consequence

The generic `FLT-BRAUER-NESBITT` obligation must not be marked proved or replaced globally. The
residual specialization may be consumed later by `FLT-MLT-COEFFICIENTS` after its hypotheses are
proved. The characteristic-zero compatible-family branch remains a distinct open theorem.
