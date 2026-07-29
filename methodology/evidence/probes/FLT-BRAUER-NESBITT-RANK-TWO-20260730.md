# FLT Brauer–Nesbitt rank-two evidence packet

## Claim

At code commit `7a6603ee7c1003dc95deb8074376cc5c09a1b60a`, the repository contains a
kernel-checked theorem that two finite-dimensional semisimple representations
of rank two over an arbitrary field are equivalent when their characteristic
polynomials agree on every group element.

Public declarations:

- `FLT.Components.BrauerNesbitt.nonempty_representationEquiv_of_finrank_eq_two`
- `FLT.Components.BrauerNesbitt.RankTwoContract`
- `FLT.Components.BrauerNesbitt.rankTwoContract`
- `FLT.Components.BrauerNesbitt.SemisimpleAlgebra.nonempty_linearEquiv_of_charpoly_eq`

## Producer verification

- Targeted command: `lake build FLT.Components.BrauerNesbitt.RankTwo FLTMethodology.Probes.BrauerNesbittRankTwo`
- Result: success; 2,322 jobs
- Umbrella command: `lake build FLT`
- Result: success; 8,990 jobs
- `git diff --check`: success
- Declaration-level axiom result for each public declaration:
  `[propext, Classical.choice, Quot.sound]`
- `sorryAx`: absent from every audited public declaration

## Live consumer discharge

`FLTMethodology.Taylor2018.Coefficients.latticeIndependent_rankTwo` now proves
the bounded coefficient-data lattice-independence consumer without accepting a
Brauer--Nesbitt contract as an argument. The two `CoefficientData` bundles
provide semisimplicity and rank two; the pre-existing integral-model lemmas
provide characteristic-polynomial equality.

- Consumer declarations:
  `latticeIndependent_rankTwo`, `latticeIndependent_rankTwo'`
- Consumer build:
  `lake build FLTMethodology.Probes.MLTCoefficientData
  FLTMethodology.Probes.BrauerNesbittRankTwo`
- Result: success; 3,851 jobs
- Consumer axiom result: `[propext, Classical.choice, Quot.sound]`
- Full command: `lake build FLT FLTMethodology`
- Result: success; 9,043 jobs

An initial combined probe attempt failed because a `module` file cannot import
the older non-`module` coefficient probe. The proof file itself compiled in that
attempt. The audit prints were moved to the coefficient probe's own surface and
the same combined targets then passed. This administrative failure is retained
here rather than hidden.

## Independent assurance

- Fable 5: positive static mathematical assessment; executable phase unavailable
  because the session could not leave plan mode. This is corroboration, not an
  approval gate.
- GPT-5.6 xhigh fresh independent session: `PASS`, after mathematical inspection,
  fresh targeted/umbrella elaboration, and declaration-level axiom audit.
- The first graph-promotion review returned `REVISE` for three control-plane
  inconsistencies. After repair, a fresh independent re-review returned `PASS`
  with byte-for-byte generator replay, 55 obligations, 102 edges, no cycles,
  and a repeated 9,043-job umbrella build.

Exact review records are adjacent under
`methodology/review/flt-completion/brauer-nesbitt/`.

## Promotion boundary

This evidence supports **kernel-clean, independently reviewed, bounded rank-two
Brauer–Nesbitt**, and a kernel-clean direct discharge of the currently encoded
coefficient/lattice consumer. The compatible-family consumer still depends on
the separate Chebotarev passage from almost-all Frobenius data to the theorem's
all-group-element premise.

It does not establish:

- the arbitrary-dimensional `Contract`;
- Chebotarev or the passage from almost-all Frobenius data to all group elements;
- the premises of any residual or characteristic-zero consumer;
- Fermat's Last Theorem.
