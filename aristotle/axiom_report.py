#!/usr/bin/env python3
"""Save AXLE ``#print axioms`` output for independently verified targets.

The report reruns the exact selected artifact with ``#check`` and ``#print axioms``
for the expected fully qualified target.  Missing output is indeterminate, never
silently interpreted as axiom-free.
"""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import axle_client as ax  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
BEST = ROOT / "best_proofs"
MANIFEST = BEST / "manifest.json"
AXLE = ROOT / "axle_verify.json"
PRIORITY = ROOT / "priority_reconciliation_2026-08-13.json"
OUT = ROOT / "axiom_reports"
INDEX = OUT / "index.json"
MAX = int(os.environ.get("AXIOM_MAX", "40"))
PACE = float(os.environ.get("AXIOM_PACE", "1.0"))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def normalize(content: str) -> str:
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    return "\n".join(imports + [""] + body)


def flatten_strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from flatten_strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from flatten_strings(item)


def parse_axioms(strings):
    relevant = [value for value in strings if "axiom" in value.lower() or "depends on" in value.lower()]
    axioms = set()
    saw_list = False
    for value in relevant:
        for bracketed in re.findall(r"\[([^\]]*)\]", value):
            saw_list = True
            for token in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", bracketed):
                axioms.add(token)
    return relevant, sorted(axioms), saw_list


def safe_name(target):
    return re.sub(r"[^A-Za-z0-9]+", "_", target).strip("_") + ".json"


def main():
    OUT.mkdir(exist_ok=True)
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    axle_state = json.loads(AXLE.read_text()) if AXLE.exists() else {}
    index = json.loads(INDEX.read_text()) if INDEX.exists() else {}
    priority_data = json.loads(PRIORITY.read_text()) if PRIORITY.exists() else {"targets": []}
    priority = [record["target"] for record in priority_data.get("targets", [])]
    remaining = sorted(set(manifest).difference(priority))

    todo = []
    for target in priority + remaining:
        selected = manifest.get(target, {})
        artifact = selected.get("artifact_file")
        path = BEST / artifact if artifact else None
        if not path or not path.exists() or axle_state.get(artifact, {}).get("verified") is not True:
            continue
        content = normalize(path.read_text(errors="ignore"))
        source_sha = hashlib.sha256(content.encode()).hexdigest()
        previous = index.get(target, {})
        if previous.get("source_sha256") == source_sha and previous.get("status") in {
            "standard_axioms_only",
            "nonstandard_axioms",
        }:
            continue
        todo.append((target, artifact, content, source_sha))
        if len(todo) >= MAX:
            break

    print(f"saving axiom reports for {len(todo)} AXLE-verified targets (priority first)")
    for target, artifact, content, source_sha in todo:
        probe = content.rstrip() + f"\n\n#check {target}\n#print axioms {target}\n"
        try:
            result = ax.check(probe)
            messages = (result.raw or {}).get("lean_messages") or {}
            strings = list(flatten_strings(messages))
            output, axioms, saw_list = parse_axioms(strings)
            if not result.verified:
                status = "report_failed"
            elif not output or not saw_list:
                status = "output_missing"
            elif set(axioms).difference(ALLOWED):
                status = "nonstandard_axioms"
            else:
                status = "standard_axioms_only"
            record = {
                "target": target,
                "artifact_file": artifact,
                "source_sha256": source_sha,
                "environment": result.environment,
                "status": status,
                "reported_axioms": axioms,
                "allowed_standard_axioms": sorted(ALLOWED),
                "print_axioms_output": output,
                "lean_messages": messages,
                "errors": result.errors,
                "failed_declarations": result.failed_declarations,
            }
        except Exception as exc:  # noqa: BLE001
            record = {
                "target": target,
                "artifact_file": artifact,
                "source_sha256": source_sha,
                "status": "indeterminate",
                "error": str(exc)[:500],
            }
        (OUT / safe_name(target)).write_text(json.dumps(record, indent=2) + "\n")
        index[target] = record
        INDEX.write_text(json.dumps(index, indent=2) + "\n")
        print(f"  {record['status']} {target}")
        time.sleep(PACE)

    counts = {}
    for record in index.values():
        counts[record.get("status", "unknown")] = counts.get(record.get("status", "unknown"), 0) + 1
    print(f"axiom report index: {len(index)} targets {counts}")


if __name__ == "__main__":
    main()
