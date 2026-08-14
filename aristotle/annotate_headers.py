#!/usr/bin/env python3
"""Create human-readable preview copies of V4/V5 selected proof artifacts.

The output is a comment-annotated preview and is not byte-identical to the AXLE input.
Release automation ships the exact V5-checked artifact from ``best_proofs`` instead.
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import titles  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
BEST = ROOT / "best_proofs"
OUT = ROOT / "pr_ready"
AXLE = ROOT / "axle_verify.json"
MANIFEST = BEST / "manifest.json"
HARVEST = ROOT / "harvest_ledger.json"
QUEUE_FILES = [
    "domains_queue.json",
    "mined_queue.json",
    "next_100.json",
    "pca_lean_queue.json",
    "frontier_queue.json",
    "frontier2.json",
    "reattack_queue.json",
    "frontier_spectral.json",
    "frontier_betrothed_queue.json",
    "frontier_linalg.json",
    "frontier_riemann.json",
    "frontier_infinity.json",
    "frontier_fibonacci.json",
    "frontier_primes.json",
    "frontier_rh2.json",
    "frontier_wave2.json",
    "frontier_wave3.json",
    "frontier_wave4.json",
    "frontier_wave5.json",
]


def normalize(content):
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    text = "\n".join(body)
    text = re.sub(r"\A\s*/-!.*?-/\s*", "", text, count=1, flags=re.S)
    return "\n".join(imports), text.lstrip("\n")


def main():
    axle = json.loads(AXLE.read_text()) if AXLE.exists() else {}
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    harvest = json.loads(HARVEST.read_text()) if HARVEST.exists() else {}
    tier_of = {}
    for meta in harvest.values():
        if meta.get("verdict") == "PROVED" and meta.get("target"):
            tier_of.setdefault(meta["target"], meta.get("tier"))
    statements = {}
    for queue_name in QUEUE_FILES:
        path = ROOT / queue_name
        if not path.exists():
            continue
        data = json.loads(path.read_text())
        items = data.get("queue", []) if isinstance(data, dict) else data
        for item in items:
            statements.setdefault(item["target"], item.get("statement"))

    OUT.mkdir(exist_ok=True)
    done = 0
    for target, selected in sorted(manifest.items()):
        artifact = selected.get("artifact_file")
        if not artifact or axle.get(artifact, {}).get("verified") is not True:
            continue
        source = BEST / artifact
        if not source.exists():
            continue
        imports, body = normalize(source.read_text(errors="ignore"))
        header = titles.header(target, tier_of.get(target), statements.get(target), verified=True)
        (OUT / artifact).write_text(header + "\n\n" + imports + "\n\n" + body + "\n")
        done += 1
    print(f"annotated {done} AXLE-passing preview copies -> {OUT}/")
    print("release automation uses exact V5-checked best_proofs artifacts, not these previews")


if __name__ == "__main__":
    main()
