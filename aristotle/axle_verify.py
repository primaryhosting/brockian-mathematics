#!/usr/bin/env python3
"""Independently compile selected proof artifacts with AXLE.

Priority reconciliation targets run first.  A cached indeterminate/missing-hash record
is always retried, and an expected target-name mismatch is a hard failure even when the
file otherwise compiles.
"""
import glob
import hashlib
import json
import os
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import axle_client as ax  # noqa: E402

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from proof_identity import declaration_signatures, target_is_represented  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "best_proofs"
STATE = ROOT / "axle_verify.json"
MANIFEST = SRC / "manifest.json"
PRIORITY = ROOT / "priority_reconciliation_2026-08-13.json"
MAX = int(os.environ.get("AXLE_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))


def normalize(content: str) -> str:
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    return "\n".join(imports + [""] + body)


def digest(content: str) -> str:
    return hashlib.sha256(content.encode()).hexdigest()


def ordered_files(files, manifest, priority):
    by_name = {pathlib.Path(path).name: path for path in files}
    ordered = []
    for target in priority:
        artifact = manifest.get(target, {}).get("artifact_file")
        if artifact in by_name:
            ordered.append(by_name.pop(artifact))
    ordered.extend(by_name[name] for name in sorted(by_name))
    return ordered


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    reverse = {meta.get("artifact_file"): target for target, meta in manifest.items()}
    priority_data = json.loads(PRIORITY.read_text()) if PRIORITY.exists() else {"targets": []}
    priority = [record["target"] for record in priority_data.get("targets", [])]
    files = ordered_files(sorted(glob.glob(str(SRC / "*.lean"))), manifest, priority)

    def stale(path):
        filename = pathlib.Path(path).name
        previous = state.get(filename)
        current_hash = digest(normalize(pathlib.Path(path).read_text(errors="ignore")))
        return (
            previous is None
            or previous.get("verified") is None
            or not previous.get("source_sha256")
            or previous.get("source_sha256") != current_hash
        )

    todo = [path for path in files if stale(path)][:MAX]
    print(f"{len(files)} selected proofs; AXLE-verifying {len(todo)} (priority first)")
    for path in todo:
        filename = pathlib.Path(path).name
        content = normalize(pathlib.Path(path).read_text(errors="ignore"))
        source_sha = digest(content)
        declarations = declaration_signatures(content)
        target = reverse.get(filename)
        represented = target_is_represented(target, declarations) if target else None
        try:
            result = ax.check(content)
            verified = result.verified and represented is not False
            errors = list(result.errors[:2])
            if represented is False:
                errors.append(f"expected target declaration not represented: {target}")
            state[filename] = {
                "verified": verified,
                "environment": result.environment,
                "errors": errors,
                "failed_declarations": result.failed_declarations[:4],
                "source_sha256": source_sha,
                "hash": source_sha[:16],
                "target": target,
                "expected_target_represented": represented,
                "declarations": declarations,
            }
        except Exception as exc:  # noqa: BLE001
            state[filename] = {
                "verified": None,
                "error": str(exc)[:500],
                "source_sha256": source_sha,
                "hash": source_sha[:16],
                "target": target,
                "expected_target_represented": represented,
                "declarations": declarations,
            }
        STATE.write_text(json.dumps(state, indent=1))
        verdict = state[filename].get("verified")
        mark = "OK " if verdict else (".. " if verdict is None else "xx ")
        detail = state[filename].get("errors") or state[filename].get("error", "")
        print(f"  {mark}{filename}" + ("" if verdict else f"  {detail}"))
        time.sleep(PACE)

    verified = sum(1 for record in state.values() if record.get("verified") is True)
    failed = sum(1 for record in state.values() if record.get("verified") is False)
    indeterminate = sum(1 for record in state.values() if record.get("verified") is None)
    print(
        f"\nAXLE verified {verified} | failed {failed} | indeterminate {indeterminate} | "
        f"records {len(state)}/{len(files)}"
    )


if __name__ == "__main__":
    main()
