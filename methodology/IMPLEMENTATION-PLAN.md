# FLT implementation programme

This is an independent methodology experiment on a frozen public snapshot. It is not affiliated
with or endorsed by Imperial College London. The upstream project and its blueprint remain
authoritative. An elaborating scaffold is not a proof, and upstream admissions are development
boundaries rather than defects.

## Current adjudication

The programme is **not yet authorized for unrestricted proof burn-down**. Opus 4.8 returned
`REVISE`; its graph repairs have been incorporated. The exact requested Sonnet 5.0 model was not
available, so the independent Lean-architecture and cross-review gates remain open. More
importantly, `FLT-MLT-SOURCE` is still a genuine source/statement gap: neither candidate
modularity-lifting theorem currently matches the blueprint target without additional proved
bridges.

The safe next construction tranche is restricted to source-independent leaves. It must not enter
modularity lifting, potential modularity, or compatible families until their signatures are
source-frozen and reviewed.

## Discovery and proof direction

Discovery proceeds from `PNat.pow_add_pow_ne_pow` down through `flt`, B1--B4, generic
hardly-ramified reducibility, characteristic-zero lifts, compatible families, potential
modularity, modularity lifting, and their foundations. Construction reverses that order within
each dependency component.

The current graph has 49 nodes and 77 direct edges. Forty-eight nodes are on the intended critical
closure. There are no graph cycles after separating the blueprint-temporary S-good condition from
the source-selected condition. The longest dependency depth is 18.

## Milestones

### T1 — sorry-free modulo the visible 1980s authority

Every T1 node is kernel-clean; the top theorem has no `sorryAx`; `knownin1980s` is permitted only as
an explicitly visible dependency. Current graph estimate:

| Quantile | Lean LOC | model output tokens |
|---|---:|---:|
| P50 | 336,650 | 43,063,500 |
| P80 | 1,508,250 | 243,922,000 |
| P95 | 6,050,850 | 1,280,604,000 |

### T2 — finite named historical interface

The generic authority is replaced by exact, typed, sourced assumptions. The interface-freeze work
is small compared with proving those theorems, but source reconciliation can still repair types.
A planning allowance is 3,000 / 15,000 / 60,000 LOC at P50/P80/P95 and 0.4 / 2.5 / 15 million
output tokens. This does not count as unconditional proof.

### T3 — unconditional kernel-clean FLT

Every named historical obligation is proved and the top axiom closure is exactly the standard
trio. The ten T2-first nodes remain explicitly load-bearing at T3 through each node's
`completion_targets` and `stage_completion`. The current cumulative graph estimate is:

| Quantile | Lean LOC | model output tokens |
|---|---:|---:|
| P50 | 484,650 | 61,483,500 |
| P80 | 2,240,250 | 354,572,000 |
| P95 | 9,020,850 | 1,887,404,000 |

These are heavy-tailed programme sizes, not completion dates. The P95 tail reflects missing
automorphic, p-adic Hodge, deformation, algebraic-geometric, and analytic interfaces and can grow
when an exact source theorem forces a different architecture.

## Execution waves

`control/wave-plan.ndjson` is the machine-readable schedule. The principal waves are:

1. source and signature repair for the modularity-lifting boundary;
2. frozen definitions and exact library contracts;
3. decomposed Tate/torsion/Frey support;
4. finite historical-interface freeze, with unconditional discharge continuing in parallel;
5. deformation and automorphic/Galois foundations;
6. auxiliary-field and residual-image construction;
7. Taylor-Wiles patching and the selected lifting theorem;
8. potential modularity, lifts, and compatible families;
9. mod-3 and 3-adic classification;
10. compatible-family comparison and generic reducibility;
11. B4 and the existing boss-chain assembly;
12. T2/T3 historical discharge and final axiom audits.

The schedule is a partial order. Tate support has four safe parallel leaves. Deformation and
automorphic foundations can proceed in separate worktrees only after their signatures are frozen.
Historical theorem formalizations can run independently but join at T3. Patching, potential
modularity, compatible families, the terminal comparison, and the boss chain are serialized join
points.

## Review and kernel gates

Every theorem cluster must satisfy, in order:

1. exact source and Lean signature frozen;
2. temporary specialization probe elaborates;
3. leaf declarations compile without `sorryAx` or unapproved custom axioms;
4. one independent review checks the load-bearing source and interface;
5. downstream imports consume the reviewed declaration;
6. the monitor records the exact axiom closure.

Useful reviews are expected at the source-selection gate, the four large programme joins, each
historical-interface family, B4 assembly, and the T1/T2/T3 terminal audits. The expected useful
range is 24--43 evidence-producing reviews across the whole programme. A second review cycle is
permitted only after new source or kernel evidence. Style-only loops stop after one pass.

## Checkpoint and rollback

- One governed branch or worktree owns each source file.
- Commit only kernel-green leaves or explicitly labelled methodology scaffolds outside the verified
  root.
- Never move an admission to claim progress.
- Before a downstream join, record declaration type, axiom closure, source locator, and reviewer
  verdict.
- If a signature is refuted, preserve the counterprobe, revert only the unpublished dependent
  tranche, and return the node to `definition-gap` or `blocked`.
- Rebase on upstream only as a separately reviewed experiment; this programme remains pinned to
  the frozen SHA.

## Exact completion test

A node closes only when its intended declaration exists with the frozen type, builds, has the
target-stage axiom closure, has no replacement `sorry`, `admit`, custom axiom, `unsafe`, or
`native_decide`, has its source conditions reconciled, is reviewed where load-bearing, and is
recorded by the monitor. G4, G5, and G6 are terminal kernel gates, not source-grep counters.

## First safe proof leaf

The first source-independent proof candidate is `group_theory_lemma` in
`FLT/EllipticCurve/Torsion.lean`, within `FLT-TATE-TORSION`:

```lean
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ}
    (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → ZMod n))
```

It has no dependency on the unresolved modularity-lifting interface. Its gate is a targeted module
build and a `#print axioms group_theory_lemma` result containing no `sorryAx`. The likely first
residual is matching the finite abelian group structure theorem to the cardinality hypothesis for
all divisors of `n`. Work on the two adjacent elliptic-curve division-polynomial theorems remains
out of scope unless the upstream authors' explicit coordination request is satisfied.

### First bounded construction result

The four `DistribMulAction` laws used by `WeierstrassCurve.galoisRepresentation` were closed as a
source-independent sub-tranche. `FLT.EllipticCurve.Torsion` builds and the exported instance has
axiom closure `[propext, Classical.choice, Quot.sound]`. This is a helper-level closure only:
`FLT-TATE-TORSION` remains open with five admissions in the file, including the exact
`group_theory_lemma` leaf above.
