# Independent executable review — rank-two consumer wiring

- Task: `task:ca-flt-brauer-nesbitt-milestone-20260730`
- Reviewed code commit: `10023b2`
- Parent: `3dbc1e7`
- Reviewer: `gpt56xhigh-independent-reviewer-d10`
- Backend/model: Codex / `gpt-5.6-sol`
- Effort: `xhigh`
- Fresh session: yes
- Duration: 254,656 ms
- Exit code: 0
- Verdict: **PASS**

## Exact terminal review

> PASS
>
> 1. The delta adds only the rank-two import and two consumer declarations.
> Both elaborate with the intended exact target,
> `SemisimpleResidualEquivalent D1.rhobar D2.rhobar`.
> (`MLTCoefficientData.lean:262`)
>
> 2. The invoked theorem requires semisimplicity twice, finrank two twice, and
> characteristic-polynomial equality for every group element—without
> algebraic-closure, perfectness, or characteristic restrictions. The consumer
> supplies precisely those five premises. (`RankTwo.lean:31`,
> `MLTCoefficientData.lean:270`)
>
> 3. Each `CoefficientData` stores semisimplicity and residual charpoly agreement
> through `IsSemisimplifiedResidualModel`. Each finrank-two fact follows from its
> stored integral rank-two field by comparing charpoly degrees at the identity;
> it is not assumed circularly from lattice independence.
> (`MLTSourceBoundary.lean:48`, `BrauerNesbittBoundary.lean:374`,
> `MLTCoefficientData.lean:225`)
>
> 4. Pointwise residual charpoly equality is proved for every Galois element by
> comparing both integral models with the same generic `rho`, then reducing their
> charpolys. No Chebotarev or almost-all-Frobenius premise is smuggled in.
> (`MLTCoefficientData.lean:196`, `:213`)
>
> 5. The `Representation.Equiv` is converted correctly:
> `e.conj_apply_self g` has the required orientation, and `GaloisRep.ext`
> upgrades it to `D1.rhobar.conj e.toLinearEquiv = D2.rhobar`, exactly the
> equality inside `SemisimpleResidualEquivalent`.
> (`MLTCoefficientData.lean:282`, `MLTSourceBoundary.lean:64`,
> `GaloisRep.lean:62`)
>
> 6. The recorded one-sided-trace counterexample is inapplicable: this consumer
> has both ranks exactly two and full characteristic-polynomial equality. It also
> takes actual `D1` and `D2` values, so it proves comparison rather than vacuously
> asserting their existence. (`BrauerNesbittBoundary.lean:290`)
>
> 7. Fresh targeted elaborations of `MLTCoefficientData.lean` and
> `BrauerNesbittRankTwo.lean` succeeded. Both new declarations and the provider
> audit to exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`,
> `admit`, `knownin1980s`, custom axiom, or unsafe dependency occurs in their
> transitive closure. `lake build FLT FLTMethodology` also completed successfully
> with 9,043 jobs. This meets the strict T3 axiom set but closes only the encoded
> same-coefficient-field rank-two lattice consumer—not Chebotarev, other
> coefficient providers, the general-dimensional contract, or FLT.

## Scope of approval

The verdict approves the direct rank-two coefficient/lattice consumer wiring.
It does not approve a general-dimensional theorem, the other coefficient
providers, Chebotarev, the compatible-family terminal, or FLT.
