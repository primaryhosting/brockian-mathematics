#!/usr/bin/env python3
"""Run pinned-repository local Lean checks over harvested candidates.

Local success is recorded as V3 evidence only.  This stage never emits an eligible
registry promotion by itself; promotion requires the later AXLE, expected-target, and
saved-axiom gates recorded by ``reconcile_proofs.py``.
"""
import concurrent.futures as futures
import glob
import hashlib
import json
import os
import pathlib
import subprocess

try:
    from proof_identity import declaration_signatures, target_is_represented
except ModuleNotFoundError:  # imported as a package in tests/tools
    from .proof_identity import declaration_signatures, target_is_represented

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
OUT = ROOT / "harvest_100"
STATE = OUT / "verify_state.json"
PROPOSED = OUT / "proposed_promotions.json"
REPORT = OUT / "verify_report.md"
TIMEOUT = int(os.environ.get("VERIFY_TIMEOUT", "1500"))
WORKERS = int(os.environ.get("VERIFY_WORKERS", "2"))


def source_sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def repository_revision():
    process = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO, capture_output=True, text=True, timeout=20
    )
    return process.stdout.strip() if process.returncode == 0 else None


def lean_version():
    process = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=60,
    )
    return ((process.stdout or "") + (process.stderr or "")).strip()[:300]


def verify_one(path):
    sha = source_sha(path)
    try:
        process = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=REPO,
            capture_output=True,
            text=True,
            timeout=TIMEOUT,
        )
        output = (process.stderr or "") + (process.stdout or "")
        ok = process.returncode == 0 and "error:" not in output.lower()
        return path, ok, ("" if ok else output[:1000]), sha
    except subprocess.TimeoutExpired:
        return path, None, f"timeout >{TIMEOUT}s", sha
    except Exception as exc:  # noqa: BLE001
        return path, None, str(exc)[:500], sha


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    files = sorted(glob.glob(str(OUT / "*.lean")))

    def stale(path):
        filename = os.path.basename(path)
        previous = state.get(filename)
        return (
            previous is None
            or previous.get("compiles") is None
            or previous.get("source_sha256") != source_sha(path)
        )

    todo = [path for path in files if stale(path)]
    revision = repository_revision()
    version = lean_version()
    print(f"{len(files)} candidates, {len(todo)} to verify ({WORKERS} workers, {TIMEOUT}s cap)")

    with futures.ThreadPoolExecutor(max_workers=WORKERS) as executor:
        for path, ok, detail, sha in executor.map(verify_one, todo):
            filename = os.path.basename(path)
            text = pathlib.Path(path).read_text(errors="ignore")
            declarations = declaration_signatures(text)
            state[filename] = {
                "compiles": ok,
                "detail": detail,
                "source_sha256": sha,
                "repository_revision": revision,
                "lean_version": version,
                "declarations": declarations,
            }
            STATE.write_text(json.dumps(state, indent=1))
            mark = "OK " if ok else (".. " if ok is None else "xx ")
            print(f"  {mark}{filename} {detail[:100]}")

    # Preserve the historical file path, but make every record explicitly ineligible.
    # reconcile_proofs.py is the only component that may mark a V5 target promotable.
    local_candidates = {}
    ledger_path = ROOT / "harvest_ledger.json"
    ledger = json.loads(ledger_path.read_text()) if ledger_path.exists() else {}
    by_filename = {}
    for project_id, meta in ledger.items():
        for filename in (f"{meta.get('account')}_{project_id}.lean", f"{meta.get('account')}_{project_id[:8]}.lean"):
            by_filename[filename] = meta.get("target")
    for filename, record in state.items():
        if record.get("compiles") is not True:
            continue
        target = by_filename.get(filename)
        represented = target_is_represented(target, record.get("declarations", [])) if target else False
        if target:
            local_candidates[target] = {
                "proof_file": filename,
                "local_compile": True,
                "target_represented": represented,
                "promotion_eligible": False,
                "reason": "V3 local evidence only; AXLE and saved axiom report required",
            }
    PROPOSED.write_text(json.dumps(local_candidates, indent=1) + "\n")

    verified = [name for name, record in state.items() if record.get("compiles") is True]
    failed = [name for name, record in state.items() if record.get("compiles") is False]
    pending = [name for name, record in state.items() if record.get("compiles") is None]
    lines = [
        f"# local verify — {len(verified)}/{len(state)} compiled",
        f"- local Lean V3 evidence: {len(verified)}",
        f"- failed: {len(failed)}",
        f"- timed out/indeterminate: {len(pending)}",
        "- promotion-eligible from this stage: 0",
        f"- repository revision: `{revision}`",
        f"- Lean: `{version}`",
        "",
        "## Failed / indeterminate",
    ]
    for filename, record in state.items():
        if record.get("compiles") is not True:
            lines.append(f"- {filename}: {record.get('detail', '')[:240]}")
    REPORT.write_text("\n".join(lines) + "\n")
    print(
        f"\nlocal V3 {len(verified)} | failed {len(failed)} | indeterminate {len(pending)} | "
        "promotion eligible 0"
    )


if __name__ == "__main__":
    main()
