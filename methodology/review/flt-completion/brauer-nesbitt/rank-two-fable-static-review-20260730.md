# Fable static review — rank-two Brauer–Nesbitt

- Task: `task:ca-flt-brauer-nesbitt-milestone-20260730`
- Reviewed code commit: `7a6603ee7c1003dc95deb8074376cc5c09a1b60a`
- Parent: `80551f00ff4cb8697cf2db605f289c18f735382b`
- Reviewer: `fable5-designer-d10`
- Duration: 461,025 ms
- Classification: positive static mathematical review; **not an executable approval**

## Limitation

The Fable session was forced into plan mode and had no available `ExitPlanMode`
tool. It therefore did not run its planned independent rebuild and axiom audit.
This record must not be represented as a terminal `PASS` or promotion authority.

## Reviewer response

> The read-only phase of this hostile review is complete, and the load-bearing
> mathematical checks all passed by hand: the degree-two Amitsur identity
> `det(A+B) = detA + detB + trA·trB − tr(AB)` is denominator-free (I expanded it
> entry-wise — it holds in char 2 and over F₂, so no cardinality/perfectness
> escape hatch is hidden there), the idempotent-charpoly trick
> `X^(n−r)(X−1)^r` recovers block ranks over any field because `X` and `X−1`
> are always coprime, and the Wedderburn reconstruction stays over
> possibly-noncommutative division rings by cancelling `finrank k (D i)` and
> `card ι` (both provably positive) instead of passing to a splitting field.

The reviewer also reported that the Mathlib sources and signatures were
present, found no textual `sorry`, `axiom`, `unsafe`, or `native_decide` in the
reviewed chain, classified the statement as bounded and non-circular, and
identified the repository-wide `warn.sorry = false` setting as a reason that an
explicit axiom audit remained mandatory.

## Required disposition

Retain this as corroborating mathematical review only. The executable review
and kernel evidence are recorded separately.
