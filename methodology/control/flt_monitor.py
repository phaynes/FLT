#!/usr/bin/env python3
"""Fail-closed monitor for the public FLT methodology experiment."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
from pathlib import Path


BASELINE = "ee47fd2abea29d0007dfed9c3c7cad2b1f4d642b"
TASK_ID = "task:fg-flt-proof-methodology-plan-20260716"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
T1_AXIOMS = STANDARD_AXIOMS | {"knownin1980s"}
ROOT = Path(__file__).resolve().parents[2]


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=False)


def ndjson(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def source_admissions(paths: list[Path]) -> int:
    pattern = re.compile(r"^\s*sorry\b|:=\s*sorry\b|\bby\s+sorry\b")
    count = 0
    files: list[Path] = []
    for path in paths:
        files.extend(path.rglob("*.lean") if path.is_dir() else [path])
    for path in files:
        count += sum(bool(pattern.search(line)) for line in path.read_text().splitlines())
    return count


def parse_axioms(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
    for name, body in pattern.findall(output):
        result[name] = [item.strip() for item in body.split(",") if item.strip()]
    return result


parser = argparse.ArgumentParser()
parser.add_argument("--build", action="store_true", help="run the warm FLT and methodology builds")
parser.add_argument(
    "--emit",
    default="methodology/output/flt-progress.ndjson",
    help="append destination relative to the repository root",
)
args = parser.parse_args()

sha = run("git", "rev-parse", "HEAD").stdout.strip()
baseline_is_ancestor = run("git", "merge-base", "--is-ancestor", BASELINE, "HEAD").returncode == 0
lean_version = run("lake", "env", "lean", "--version").stdout.splitlines()[0].strip()

build_results: dict[str, object] = {"requested": args.build, "FLT": None, "FLTMethodology": None}
if args.build:
    flt_build = run("lake", "build", "FLT")
    methodology_build = run(
        "lake",
        "build",
        "FLTMethodology.Scaffold",
        "FLTMethodology.Probes.ExistingContracts",
        "FLTMethodology.Probes.GaloisRepresentationActionAudit",
        "FLTMethodology.Probes.LibraryMatches",
    )
    build_results.update(
        {
            "FLT": flt_build.returncode == 0,
            "FLTMethodology": methodology_build.returncode == 0,
            "flt_tail": (flt_build.stdout + flt_build.stderr).splitlines()[-5:],
            "methodology_tail": (methodology_build.stdout + methodology_build.stderr).splitlines()[-5:],
        }
    )

audit = run("lake", "env", "lean", "methodology/evidence/baseline/MonitorAudit.lean")
axioms = parse_axioms(audit.stdout + audit.stderr)
top_axioms = axioms.get("PNat.pow_add_pow_ne_pow", [])

obligations = ndjson(ROOT / "methodology/control/proof-obligations.ndjson")
scaffold_ledger = ndjson(ROOT / "methodology/control/scaffold-admissions.ndjson")
historical_ledger = ndjson(ROOT / "methodology/control/historical-assumptions.ndjson")
t2_named_axioms = {
    row["lean_axiom"]
    for row in historical_ledger
    if row.get("status") == "permitted" and isinstance(row.get("lean_axiom"), str)
}
scaffold_actual = source_admissions([ROOT / "FLTMethodology"])
verified_admissions = source_admissions([ROOT / "FLT", ROOT / "FLT.lean", ROOT / "FermatsLastTheorem.lean"])
state_counts: dict[str, int] = {}
for node in obligations:
    state_counts[node["current_state"]] = state_counts.get(node["current_state"], 0) + 1
critical_open = sum(
    node["critical_path"] and node["kernel_probe_state"] not in {"proof-green", "integrated"}
    for node in obligations
)

varro_evidence = json.loads((ROOT / "methodology/evidence/varro-validation.json").read_text())
varro_source = ROOT / varro_evidence["source"]
varro_hash = hashlib.sha256(varro_source.read_bytes()).hexdigest()
varro_valid = bool(varro_evidence["valid"] and varro_hash == varro_evidence["source_sha256"])

review_root = ROOT / "methodology/review"
convergence_path = review_root / "CONVERGENCE.md"
sonnet_path = review_root / "sonnet50-initial.md"
opus_path = review_root / "opus48-initial.md"
sonnet_complete = sonnet_path.exists() and "NOT RUN" not in sonnet_path.read_text()
opus_complete = opus_path.exists() and "NOT RUN" not in opus_path.read_text()
convergence_text = convergence_path.read_text() if convergence_path.exists() else ""
review_complete = bool(
    sonnet_complete
    and opus_complete
    and "REVIEW CONVERGED" in convergence_text
    and "LOAD-BEARING BLOCKER" not in convergence_text
)
obligation_ids = {node["obligation_id"] for node in obligations}
stage_coverage = sorted(
    {stage for node in obligations for stage in node.get("completion_targets", [])}
)
graph_valid = bool(
    len(obligation_ids) == len(obligations)
    and all(set(node["direct_dependencies"]) <= obligation_ids for node in obligations)
    and all(node["target_stage"] in node.get("completion_targets", []) for node in obligations)
    and stage_coverage == ["T1", "T2", "T3"]
)
scaffold_enumerated = scaffold_actual == len(scaffold_ledger)

gates = {
    "G0": bool(baseline_is_ancestor and audit.returncode == 0 and build_results["FLT"] is True),
    "G1": bool(graph_valid and varro_valid and review_complete),
    "G2": bool(scaffold_enumerated and build_results["FLTMethodology"] is True and review_complete),
    "G3": bool(
        graph_valid
        and all(
            node["kernel_probe_state"] != "proof-green" or node["current_state"] != "absent"
            for node in obligations
        )
    ),
    "G4": bool(top_axioms and "sorryAx" not in top_axioms and set(top_axioms) <= T1_AXIOMS),
    "G5": bool(
        top_axioms
        and "sorryAx" not in top_axioms
        and "knownin1980s" not in top_axioms
        and set(top_axioms) <= STANDARD_AXIOMS | t2_named_axioms
    ),
    "G6": bool(set(top_axioms) == STANDARD_AXIOMS),
}
current_gate = next((gate for gate in ("G0", "G1", "G2", "G3", "G4", "G5", "G6") if not gates[gate]), "complete")

record = {
    "timestamp": dt.datetime.now(dt.timezone.utc).isoformat(),
    "git_sha": sha,
    "frozen_baseline_sha": BASELINE,
    "task_id": TASK_ID,
    "lean_version": lean_version,
    "build_result": build_results,
    "audit_result": audit.returncode == 0,
    "target_declarations": {
        name: {"present": name in axioms, "axioms": closure, "sorryAx": "sorryAx" in closure, "knownin1980s": "knownin1980s" in closure}
        for name, closure in axioms.items()
    },
    "scaffold_admissions": {"actual": scaffold_actual, "ledger": len(scaffold_ledger), "enumerated": scaffold_enumerated},
    "verified_root_admissions": verified_admissions,
    "historical_assumptions": {
        "permitted_t2_axioms": sorted(t2_named_axioms),
        "generic_knownin1980s_present": "knownin1980s" in top_axioms,
    },
    "graph": {
        "nodes": len(obligations),
        "state_counts": state_counts,
        "critical_path_open": critical_open,
        "completion_target_coverage": stage_coverage,
        "valid": graph_valid,
    },
    "current_gate": current_gate,
    "gates": gates,
    "review_state": {
        "converged": review_complete,
        "sonnet_complete": sonnet_complete,
        "opus_complete": opus_complete,
    },
    "source_validation": (ROOT / "methodology/SOURCE-REGISTER.md").exists(),
    "varro_validation": {"valid": varro_valid, "source_sha256": varro_hash},
}

destination = ROOT / args.emit
destination.parent.mkdir(parents=True, exist_ok=True)
with destination.open("a") as stream:
    stream.write(json.dumps(record, sort_keys=True) + "\n")
print(json.dumps(record, indent=2, sort_keys=True))
