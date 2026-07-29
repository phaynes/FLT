# Independent executable review — rank-two Brauer–Nesbitt

- Task: `task:ca-flt-brauer-nesbitt-milestone-20260730`
- Reviewed code commit: `7a6603ee7c1003dc95deb8074376cc5c09a1b60a`
- Parent: `80551f00ff4cb8697cf2db605f289c18f735382b`
- Reviewer: `gpt56xhigh-independent-reviewer-d10`
- Backend/model: Codex / `gpt-5.6-sol`
- Effort: `xhigh`
- Fresh session: yes
- Duration: 386,087 ms
- Exit code: 0
- Verdict: **PASS**

## Exact terminal review

> PASS
>
> 1. The public theorem has the exact bounded type: arbitrary field and group,
> two finite-dimensional semisimple rank-two representations, and
> characteristic-polynomial equality for every group element.
> `RankTwoContract` repeats rather than weakens this statement, and
> `rankTwoContract` proves it without assuming `Contract` or an equivalent
> conclusion. (`RankTwo.lean:33`)
>
> 2. The degree-two Amitsur step is valid in every characteristic. It derives
> trace equality linearly, extends determinant equality using the
> denominator-free identity
> `det(A+B)=det A+det B+tr A·tr B−tr(AB)`, and then reconstructs the degree-two
> characteristic polynomial. It uses neither interpolation nor division, so
> finite fields and characteristic two introduce no gap. (`AmitsurFinTwo.lean:31`,
> `:62`, `:154`)
>
> 3. The joint-image algebra is substantive and non-circular: the group image
> spans it; semisimplicity descends through the surjective group-algebra action;
> and the faithful action on `V × W` forces the Jacobson radical to vanish. No
> Brauer–Nesbitt conclusion is used in this construction.
> (`JointImageAlgebra.lean:51`, `:95`, `:187`)
>
> 4. The Wedderburn–Artin reconstruction correctly retains possibly
> noncommutative division rings. The proof transports through the exact Mathlib
> algebra equivalence, decomposes by central coordinate idempotents, installs
> the division-ring actions through `Matrix.scalar`, proves the required scalar
> towers, and uses matrix Morita equivalence plus finite-dimensional restriction
> of scalars. No commutativity, perfectness, separability, or algebraic closure
> of the division rings is assumed. (`SemisimpleReconstruction.lean:268`, `:335`,
> `:404`; Mathlib `WedderburnArtin.lean:204`)
>
> 5. Block multiplicities are recovered correctly. For each central idempotent,
> characteristic-polynomial equality fixes the multiplicity of the root `1`,
> hence the ground-field dimension of its image. That image is exactly the
> central block component; equal component dimensions then determine the
> matrix-algebra module through Morita equivalence. This avoids the known
> failure of trace characters over purely inseparable extensions.
> (`IdempotentCharpoly.lean:32`, `SemisimpleReconstruction.lean:533`)
>
> 6. The final transports preserve the intended maps. The product-block
> equivalence is converted back through the algebra equivalence as an
> `A`-linear equivalence, and joint-image linearity at `jointImageElement g`
> proves the required intertwining equation for every group element. The result
> is genuinely `Representation.Equiv rho sigma`.
> (`SemisimpleReconstruction.lean:562`, `JointImageAlgebra.lean:152`)
>
> 7. Counterexample and source boundaries are respected. The recorded
> characteristic-two regression refutes only a trace-only weakening; the new
> theorem retains equal rank and full characteristic polynomials. The older
> source-design packet remains applicable to the arbitrary-dimensional
> `Contract`, not as evidence that this bounded theorem closes Chebotarev or the
> full `FLT-BRAUER-NESBITT` obligation. (`BrauerNesbittBoundary.lean:290`,
> `brauer-nesbitt.md:120`)
>
> 8. Kernel and build evidence passes. Fresh elaboration succeeded for both new
> implementation files, the audit probe, `FLT.lean`, and `FLTMethodology.lean`;
> `lake build FLT.Components.BrauerNesbitt.RankTwo
> FLTMethodology.Probes.BrauerNesbittRankTwo` completed 2,322 jobs, and
> `lake build FLT` completed 8,990 jobs. Every changed declaration was audited
> individually; each depends on at most `propext`, `Classical.choice`, and
> `Quot.sound`, with no `sorryAx`, custom axiom, `admit`, or unsafe declaration.
> The imports are therefore appropriate. The combined umbrella command
> encountered only a read-only permission error deleting four unrelated cached
> methodology artifacts; direct methodology elaboration passed.

## Scope of approval

The verdict approves the bounded rank-two theorem for integration. It does not
approve the arbitrary-dimensional `Contract`, any Chebotarev premise, a live
consumer discharge, or Fermat's Last Theorem.
