#!/usr/bin/env python3
"""Record the local D5 dependency closure and its exact source hashes.

This is a source/provenance inventory, not a substitute for Lean checking.
It reads only the imports reachable from Brockian.D5Research and the pinned
toolchain/manifest files. Mathlib is recorded by the Lake manifest revision.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def main() -> None:
    pending = ["Brockian.D5Research"]
    seen: dict[str, dict] = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = ROOT / (module.replace(".", "/") + ".lean")
        data = path.read_bytes()
        local = [m for m in IMPORT.findall(data.decode("utf-8")) if m.startswith("Brockian.")]
        seen[module] = {
            "module": module,
            "path": str(path.relative_to(ROOT)),
            "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data),
            "local_imports": local,
        }
        pending.extend(local)
    lake = json.loads((ROOT / "lake-manifest.json").read_text())
    result = {
        "schema_version": 1,
        "base_commit": "29426ff65b6f1fd68d594e529632eb79b5be3089",
        "checkout_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
        "dependencies": [{"name": p["name"], "rev": p.get("rev")} for p in lake["packages"]],
        "target": "Brockian.D5Research",
        "local_module_count": len(seen),
        "files": [seen[k] for k in sorted(seen)],
        "scope_note": "This inventory is not a build verdict or an axiom audit.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
