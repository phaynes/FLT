# FLT-202 component-BOM audit

Date: 2026-07-16  
Task: `task:fg-flt-ra-component-bom-20260716`

## Result

```text
BOM records=52
T1 bindings=42
T2-first bindings=10
Owner work items=25
Mathematical components=31
Orphan obligations=0
FLT-405 bindings=0
Obligation graph=ACYCLIC
Component graph=ACYCLIC
Source coverage=52/52
```

The BOM obligation IDs and owner work items exactly match the independently approved programme map
in the Helios control worktree. Every binding has `coverage = "exact"`; every obligation has a
nonempty source-reference list; stages match; and every frozen obligation appears exactly once.

## Defect found and repaired

The first audit projected graph edges by `owner_work_item`. That projection reported cycles through
FLT-204. This was not a theorem-graph cycle: FLT-204 is a scheduling envelope containing several
different mathematical components, including root vocabulary and terminal boss adapters. Treating
the whole envelope as one theorem interface conflated opposite ends of the graph.

The BOM now makes the distinction binding. Its `component` field names 31 mathematical contract
components, while `owner_work_item` names 25 scheduling/review envelopes. Projection by `component`
is acyclic; projection by `owner_work_item` is invalid and is recorded as a controller requirement.

The audit also found two orphaned baseline records:

- `FLT-DEF-001` now has an explicit definition edge into `FLT-B4`.
- `FLT-HIST-QUATERNION` was misnamed as a nonexistent base-change theorem. It is now the exact
  `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ`
  instance and feeds `FLT-SUPPORT-AUTOMORPHIC`.

A kernel probe independently confirmed the corrected quaternion declaration and its current closure:

```text
[knownin1980s, propext, Classical.choice, Quot.sound]
```

This is therefore a genuine T2/T3 historical boundary rather than an unreferenced source-grep row.

## Deterministic checks

The audit parsed both NDJSON authorities with `jq`, compared sorted ID sets, checked duplicate IDs,
compared stage assignments, compared owner assignments to the approved programme map, checked all
source arrays, and projected cross-component dependency edges through `tsort`. The graph generator
then reproduced 52 obligations, 95 edges, 52 critical nodes, and zero cycles.

No proof obligation is claimed complete by this artifact. It freezes component ownership and exposes
the source/design work that FLT-205 must perform before construction starts.
