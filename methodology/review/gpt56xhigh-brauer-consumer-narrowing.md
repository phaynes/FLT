# GPT-5.6 xhigh review: Brauer--Nesbitt consumer narrowing

Candidate commit: `61ca825611de277f22289404f39ffac4df87b650`.

Model: `gpt-5.6-sol`, reasoning effort `xhigh`.

Execution: one fresh independent read-only review, 675,301 ms, followed by one same-session
evidence-only continuation, 17,597 ms. The reviewer did not receive the Fable report before its
verdict.

Verdict: **NARROWING PARTIAL ONLY**.

## Findings

- The specialized bridge elaborates and has the standard axiom trio.
- For an integral rank-two representation, the rank-two hypothesis on a residual model follows from
  characteristic-polynomial comparison at the identity and base-change finrank. The proposed proof
  was independently reproduced in `residualModel_finrank_eq_two`.
- If the residual field is the algebraic closure of a prime field of odd characteristic, algebraic
  closure and the strict `2 < ringChar` hypothesis can be supplied.
- The existing compatible family has characteristic-zero coefficient fields, so the odd residual
  branch is type-inapplicable there.
- `GaloisRepFamily.isCompatible` gives almost-all Frobenius compatibility, while the specialized
  bridge requires an all-group-element comparison. `FLT-CHEBOTAREV` and the relevant
  semisimplicity/descent results remain absent.

## Gate consequence

The residual branch can eventually use the specialization, but the generic graph umbrella cannot
be removed yet. The compatible-family consumer needs a separately typed characteristic-zero
Brauer--Nesbitt/Chebotarev route. No public theorem or top-level assumption is changed.
