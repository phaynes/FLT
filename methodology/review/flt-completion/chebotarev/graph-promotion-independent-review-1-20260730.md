# Independent graph-promotion review — first result

Agent: `gpt56xhigh-independent-reviewer-d10`

Model: `gpt-5.6-sol`

Effort: `xhigh`

Elapsed: `705243 ms` bridge total; `705241 ms` model task.

Candidate reviewed: `b5e950f5fecfc7b61ec2444c47115ed65e407866`

Whitespace-normalized response follows; wording is exact. The byte-exact transcript remains in the
session ledger named by this task's evidence record.

REVISE

The mathematical split and graph topology are sound, but the candidate is not promotable as encoded because its new state vocabulary violates the committed schema and the Fable approval is not machine-scoped to the adapter.

## Executed checks

- Worktree clean; `HEAD` is `1f877844`.
- `ee0f49e → b5e950f5 → HEAD` ancestry verified.
- `b5e950f5..HEAD` adds exactly the requested review prompt; no later Lean or control changes.
- `git diff --check 8929b77..b5e950f5` and `b5e950f5..HEAD`: clean.
- Complete `8929b77..b5e950f5` candidate diff inspected; `ee0f49e..b5e950f5` contains review/control evidence only.
- Every line parsed successfully in all five NDJSON files:

  - attempts: 125
  - execution: 15
  - graph: 159
  - obligations: 56
  - source design: 32

- Independently recomputed:

  - 56 obligation rows and 56 unique obligation IDs
  - 103 edges, edge IDs, and endpoint pairs, all unique
  - no missing endpoints, self-edges, dependency mismatches, or cycles
  - canonical obligations and edges exactly equal the corresponding sets in `flt-proof-program.instances.json`

- Direct elaboration of the current implementation and probe succeeded. All seven public theorems printed exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, density axiom, witness, or instance was found. See [the implementation](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLT/GaloisRepresentation/CompatibleFamilyComparison.lean:169) and [axiom probe](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/FLTMethodology/Probes/ChebotarevRankTwo.lean:17).
- Inspected the retained 3,629-job targeted build, 9,045-job umbrella build, Fable executable `PASS`, both GPT executable `REVISE` reviews, design evidence, raw session ledgers, source packet, and local source conversions.

## Findings, ordered by severity

1. **High — the promoted rows violate the committed instance schema.**

   The schema permits only four `review_state` values and four `kernel_probe_state` values. The candidate introduces four non-enum values across the density and comparison rows: [schema](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/spec/flt-proof-program.instances.schema.json:71), [density row](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/spec/flt-proof-program.instances.json:2109), [comparison row](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/spec/flt-proof-program.instances.json:2156).

   The file has older schema drift, but these four violations are introduced by this candidate; the prior `FLT-CHEBOTAREV` values were schema-valid. The bounded adapter state must be represented with schema-valid categories or through an explicitly governed schema extension that cannot imply full-obligation closure.

2. **High — Fable’s approval is not machine-bounded.**

   The retained prose verdict correctly approves only the deterministic adapter. However, its attempt row has `obligations:["FLT-CHEBOTAREV"]`, proposes the density node, and sets `promotion_allowed:true` without a `promotion_scope`: [attempt row](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/control/flt-completion-attempts.ndjson:125). Comparable recent bounded approvals in the same ledger carry explicit scopes.

   This must be `promotion_scope:"deterministic-adapter-only"` or `promotion_allowed:false` if that field cannot enforce scope. As written, it does not mechanically guarantee that the `PASS` cannot approve density or the family consumer.

3. **Medium — exact elapsed-time telemetry is not reproducible from the retained transcripts.**

   Models, GPT effort, token counters, transport outcomes, and content verdicts reconcile. Recorded GPT elapsed values do not equal the raw `task_complete.duration_ms` values:

   - 710,796 vs 709,968 ms
   - 509,192 vs 508,247 ms
   - 360,627 vs 359,663 ms

   The Fable success durations similarly exceed the transcript timestamp spans, apparently by wrapper overhead. That is plausible, but the successful rows lack an `elapsed_precision`/wrapper provenance field. The controller’s 9,280 ms build duration also cannot be reconstructed from its evidence packet. Record the wrapper timing source and precision, or retain transcript-native durations separately.

4. **Medium — `SRC-013` is not canonically registered for its Chebotarev use.**

   The graph and source packet use `SRC-013` for Gee Fact 2.27 and Remark 2.31, but the canonical register describes only Theorem 5.2 as a modularity-lifting near-match: [register](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/SOURCE-REGISTER.md:21), [source packet](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/source-design/chebotarev.md:41).

   The mathematics is supported: Gee gives conjugacy-saturated density and the Chebotarev–Brauer–Nesbitt comparison pattern, while Wiese supplies arithmetic Frobenius, finite Chebotarev, and the finite-quotient density route. Both remain secondary sources for this use, as the candidate honestly records. [Gee](https://arxiv.org/pdf/2202.05818), [Wiese](https://math.uni.lu/~wiese/notes/GalRep). Add those locators to `SRC-013` or assign a dedicated source ID.

5. **Low — one Fable sentence says “uninhabited” rather than “unwitnessed.”**

   The same review later uses the correct term, and all promoted control rows say “unwitnessed”: [Fable review](/Volumes/second-store/devel/proof-forks/FLT-chebotarev-rank-two-20260730/methodology/review/flt-completion/chebotarev/rank-two-adapter-fable5-executable-review-20260730.md:66). Treat the earlier wording as non-authoritative; absence of a repository witness is not a proof of uninhabitedness.

## Exact approved state transitions

Approved mathematically, but not approved for graph promotion until the control defects above are repaired:

- Add `FLT-CHEBOTAREV-DENSITY` with `current_state: absent`, owning exactly `RatArithmeticFrobeniusConjugacyDensity`.
- Add only `FLT-CHEBOTAREV-DENSITY → FLT-CHEBOTAREV`.
- Change `FLT-CHEBOTAREV.current_state` from `absent` to `definition-gap`.
- Classify the deterministic adapter at `ee0f49e` as standard-trio kernel-clean and independently reviewed.
- Preserve all existing compatible-family consumers as consumers of `FLT-CHEBOTAREV`.

No transition of either node to `proved`, `admitted`, `historical-assumption`, or terminal-complete is approved. The candidate’s `review_state` and `kernel_probe_state` transitions are not approved until expressed schema-validly without broadening the Fable approval.

## Exact remaining open boundaries

- `RatArithmeticFrobeniusConjugacyDensity` has no witness and no authorized T2 historical assumption.
- T2 density requires a separately operator-authorized, exactly typed and source-governed interface.
- T3 requires a proof of that same proposition with exactly the standard trio.
- The fixed-coefficient consumer still needs two representations over one coefficient field, fixed coefficient embeddings, semisimplicity, rank two, determinant/full-characteristic-polynomial transport, and one common finite exceptional set.
- `FLT-COMPAT-CONTRA` continues to depend on `FLT-CHEBOTAREV`.
- Neither `FLT-CHEBOTAREV`, the downstream compatible-family terminal, nor FLT is complete.

No files, commits, or task state were changed.
