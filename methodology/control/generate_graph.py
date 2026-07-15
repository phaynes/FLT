#!/usr/bin/env python3
"""Generate the derived FLT methodology graph and Varro instance document.

The canonical obligation data is `proof-obligations.ndjson`. Edges are derived from each node's
`direct_dependencies`, preventing drift between a node and the machine-readable graph.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CONTROL = ROOT / "methodology" / "control"
SPEC = ROOT / "methodology" / "spec"
BASELINE = "ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b"


def read_ndjson(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


obligations = read_ndjson(CONTROL / "proof-obligations.ndjson")
ids = {node["obligation_id"] for node in obligations}
if len(ids) != len(obligations):
    raise SystemExit("duplicate obligation ID")

# These links connect currently admitted support clusters to the theorem nodes that actually
# consume them. Keeping this normalization here makes the relationship reviewable while allowing
# the hand-authored NDJSON records to stay one record per line.
extra_dependencies = {
    "FLT-FREY-HR": ["FLT-SUPPORT-TATE"],
    "FLT-DEF-FUNCTOR": ["FLT-SUPPORT-DEFORMATION"],
    "FLT-HECKE-ACTION": ["FLT-SUPPORT-AUTOMORPHIC"],
    "FLT-JL": ["FLT-SUPPORT-AUTOMORPHIC"],
}
for node in obligations:
    for dependency in extra_dependencies.get(node["obligation_id"], []):
        if dependency not in node["direct_dependencies"]:
            node["direct_dependencies"].append(dependency)

# The present design is intended to be a DAG. Compute depth and singleton SCC identifiers from
# the actual edges; a cycle fails generation instead of being hidden by narrative ordering.
by_id = {node["obligation_id"]: node for node in obligations}
visiting: set[str] = set()
depth_cache: dict[str, int] = {}


def depth(node_id: str) -> int:
    if node_id in depth_cache:
        return depth_cache[node_id]
    if node_id in visiting:
        raise SystemExit(f"dependency cycle involving {node_id}; represent and review the SCC explicitly")
    visiting.add(node_id)
    dependencies = by_id[node_id]["direct_dependencies"]
    value = 0 if not dependencies else 1 + max(depth(dependency) for dependency in dependencies)
    visiting.remove(node_id)
    depth_cache[node_id] = value
    return value


for node in obligations:
    node["graph_depth"] = depth(node["obligation_id"])
    node["scc_id"] = f"SCC-{node['obligation_id']}"

(CONTROL / "proof-obligations.ndjson").write_text(
    "\n".join(json.dumps(node, separators=(",", ":")) for node in obligations) + "\n"
)

edges: list[dict] = []
for node in obligations:
    for dependency in node["direct_dependencies"]:
        if dependency not in ids:
            raise SystemExit(f"unknown dependency {dependency} for {node['obligation_id']}")
        edges.append(
            {
                "edge_id": f"E-{dependency.removeprefix('FLT-')}-{node['obligation_id'].removeprefix('FLT-')}",
                "from": dependency,
                "to": node["obligation_id"],
                "edge_kind": "definition" if "DEF" in dependency else "theorem",
                "justification": f"{node['obligation_id']} directly consumes {dependency}.",
            }
        )

graph_lines = [json.dumps({"record_type": "obligation", **node}, sort_keys=True) for node in obligations]
graph_lines += [json.dumps({"record_type": "edge", **edge}, sort_keys=True) for edge in edges]
(CONTROL / "proof-graph.ndjson").write_text("\n".join(graph_lines) + "\n")

targets = [
    {
        "target_id": "T1",
        "name": "Sorry-free modulo 1980s",
        "permitted_axioms": ["knownin1980s", "propext", "Classical.choice", "Quot.sound"],
        "completion_rule": "The public terminal has no sorryAx and every knownin1980s dependency is visible.",
    },
    {
        "target_id": "T2",
        "name": "Finite historical-assumption interface",
        "permitted_axioms": ["named historical assumptions", "propext", "Classical.choice", "Quot.sound"],
        "completion_rule": "The generic knownin1980s axiom is absent and every custom assumption is finite, typed, named, and sourced.",
    },
    {
        "target_id": "T3",
        "name": "Unconditional kernel-clean FLT",
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "completion_rule": "The public terminal axiom closure is exactly the standard trio.",
    },
]

gates = [
    {"gate_id": "G0", "target_stage": "methodology", "predicate": "Frozen baseline build and axiom state reproduced.", "fail_closed": True},
    {"gate_id": "G1", "target_stage": "methodology", "predicate": "Sources, contracts, complete graph, and traceability independently reviewed.", "fail_closed": True},
    {"gate_id": "G2", "target_stage": "methodology", "predicate": "Critical-path scaffold elaborates and every scaffold admission is enumerated.", "fail_closed": True},
    {"gate_id": "G3", "target_stage": "methodology", "predicate": "All proof waves are monitorable and absent targets fail closed.", "fail_closed": True},
    {"gate_id": "G4", "target_stage": "T1", "predicate": "Top theorem has no sorryAx; knownin1980s is explicitly visible.", "fail_closed": True},
    {"gate_id": "G5", "target_stage": "T2", "predicate": "knownin1980s is removed and named historical assumptions are exposed.", "fail_closed": True},
    {"gate_id": "G6", "target_stage": "T3", "predicate": "Top theorem depends only on propext, Classical.choice, and Quot.sound.", "fail_closed": True},
]

instances = {
    "baseline_sha": BASELINE,
    "targets": targets,
    "obligations": obligations,
    "edges": edges,
    "gates": gates,
}
(SPEC / "flt-proof-program.instances.json").write_text(json.dumps(instances, indent=2, sort_keys=True) + "\n")

print(
    f"obligations={len(obligations)} edges={len(edges)} "
    f"critical={sum(n['critical_path'] for n in obligations)} cycles=0"
)
