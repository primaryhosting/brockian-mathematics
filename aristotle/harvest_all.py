#!/usr/bin/env python3
"""Harvest terminal Aristotle jobs from both accounts, including direct submits.

This read-only collector labels successful downloads as remote proof candidates.
Independent Lean/AXLE verification and axiom reporting happen downstream.
"""
import glob
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import urllib.request

try:
    from proof_identity import identity_metadata
except ModuleNotFoundError:  # imported as a package in tests/tools
    from .proof_identity import identity_metadata

ROOT = pathlib.Path(__file__).resolve().parent
OUT = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
NIGHT = ROOT / "submitted_night.json"
KEYENV = {"admin": "ARISTOTLE_API_KEY", "chris": "ARISTOTLE_API_KEY_CHRIS"}
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
UUID = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")
MAXDL = int(os.environ.get("HARVEST_ALL_MAX", "200"))
PAGES = int(os.environ.get("HARVEST_ALL_PAGES", "20"))
NOTIFY = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")


def aristotle_list(key, pagination_key=None):
    args = [
        "uvx",
        "--from",
        "aristotlelib@latest",
        "aristotle",
        "list",
        "--status",
        "IDLE",
        "--limit",
        "100",
    ]
    if pagination_key:
        args += ["--pagination-key", pagination_key]
    env = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        process = subprocess.run(args, capture_output=True, text=True, env=env, timeout=120)
        output = (process.stdout or "") + "\n" + (process.stderr or "")
    except Exception:  # noqa: BLE001
        return [], None
    rows, next_key = [], None
    for line in output.splitlines():
        match = re.search(r"next page:\s*(\S+)", line)
        if match:
            next_key = match.group(1)
            continue
        stripped = line.strip()
        if UUID.match(stripped):
            project_id = stripped[:36]
            rest = re.sub(r"\bIDLE\s*$", "", stripped[36:].rstrip()).rstrip()
            name = re.sub(r"^\s*\d+\s+\w+\s+ago\s+", "", rest).strip()
            rows.append((project_id, name))
    return rows, next_key


def all_idle(key):
    seen, pagination_key = [], None
    for _ in range(PAGES):
        rows, pagination_key = aristotle_list(key, pagination_key)
        seen += rows
        if not pagination_key or not rows:
            break
    unique, ids = [], set()
    for project_id, name in seen:
        if project_id not in ids:
            ids.add(project_id)
            unique.append((project_id, name))
    return unique


def fetch(project_id, key):
    directory = tempfile.mkdtemp(prefix="harvall_")
    archive = os.path.join(directory, f"{project_id}.tar.gz")
    env = dict(os.environ, ARISTOTLE_API_KEY=key)
    try:
        subprocess.run(
            [
                "uvx",
                "--from",
                "aristotlelib@latest",
                "aristotle",
                "download",
                project_id,
                "--destination",
                archive,
            ],
            capture_output=True,
            env=env,
            timeout=180,
        )
        subprocess.run(["tar", "xzf", archive, "-C", directory], capture_output=True, timeout=60)
        lean = ""
        for path in glob.glob(os.path.join(directory, "**", "*.lean"), recursive=True):
            lean += pathlib.Path(path).read_text(errors="ignore") + "\n"
    except Exception:  # noqa: BLE001
        lean = ""
    finally:
        shutil.rmtree(directory, ignore_errors=True)
    if not lean.strip():
        return False, None, ""
    body = "\n".join(line for line in lean.splitlines() if not line.strip().startswith("--"))
    return True, ("STOPPED" if BAD.search(body) else "PROVED"), lean


def target_from(lean, name, project_id):
    namespace = None
    match = re.search(r"^\s*namespace\s+([\w.]+)", lean, re.M)
    if match:
        namespace = match.group(1)
    theorem = re.search(r"^\s*(?:theorem|lemma)\s+([\w.]+)", lean, re.M)
    if theorem:
        short = theorem.group(1)
        return (namespace + "." if namespace and not short.startswith(namespace) else "") + short
    if name:
        return "Aristotle." + re.sub(r"[^A-Za-z0-9]+", "_", name).strip("_")[:80]
    return "Aristotle.job_" + project_id[:8]


def email(subject, body):
    try:
        payload = json.dumps({"to": NOTIFY, "subject": subject, "body": body}).encode()
        request = urllib.request.Request(
            "http://127.0.0.1:18799/send",
            data=payload,
            headers={"Content-Type": "application/json"},
        )
        urllib.request.urlopen(request, timeout=30).read()
    except Exception:  # noqa: BLE001
        pass


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    night = json.loads(NIGHT.read_text()) if NIGHT.exists() else {}
    project_meta = {}
    for target, value in night.items():
        for record in value.get("ids", []):
            project_meta[record["project_id"]] = {"target": target, "tier": value.get("tier")}

    downloaded = 0
    new_proved = []
    for account, env_name in KEYENV.items():
        key = os.environ.get(env_name)
        if not key:
            print(f"{account}: no configured key; skip")
            continue
        idle = all_idle(key)
        todo = [(project_id, name) for project_id, name in idle if project_id not in ledger]
        print(f"{account}: {len(idle)} terminal jobs listed, {len(todo)} not yet harvested")
        for project_id, project_name in todo:
            if downloaded >= MAXDL:
                break
            terminal, verdict, lean = fetch(project_id, key)
            if not terminal:
                continue
            downloaded += 1
            meta = project_meta.get(project_id)
            target = meta["target"] if meta else target_from(lean, project_name, project_id)
            tier = (
                meta["tier"]
                if meta
                else (
                    "Brockian-external"
                    if "brock" in (project_name or "").lower() or "Brockian" in target
                    else "External"
                )
            )
            record = {
                "target": target,
                "account": account,
                "verdict": verdict,
                "tier": tier,
                "origin": "list" if not meta else "pipeline",
                "project_name": project_name,
                "verification_status": (
                    "remote_candidate_static_placeholder_scan"
                    if verdict == "PROVED"
                    else "remote_stopped"
                ),
            }
            if verdict == "PROVED":
                filename = f"{account}_{project_id}.lean"
                (OUT / filename).write_text(lean)
                record["source_file"] = filename
                record.update(identity_metadata(lean))
                new_proved.append((target, account))
            ledger[project_id] = record
            LEDGER.write_text(json.dumps(ledger, indent=1))
        if downloaded >= MAXDL:
            print(f"hit HARVEST_ALL_MAX={MAXDL}; rerun to continue")
            break

    proved = sum(1 for value in ledger.values() if value.get("verdict") == "PROVED")
    print(
        f"\ndownloaded {downloaded} new | +{len(new_proved)} remote PROVED candidates | "
        f"ledger now {len(ledger)} ({proved} remote PROVED candidates)"
    )
    for target, account in new_proved:
        print(f"  remote candidate {target} ({account})")
    if downloaded:
        stopped = len(ledger) - proved
        lines = [
            f"fresh two-account pull downloaded {downloaded} terminal jobs",
            f"new remote PROVED candidates {len(new_proved)}",
            f"lifetime terminal records {len(ledger)} ({proved} remote PROVED candidates; {stopped} stopped)",
            "Remote status is not local/AXLE verification and is not an axiom report.",
            "",
        ]
        lines.extend(f"  candidate {target} ({account})" for target, account in new_proved)
        email(
            f"[Aristotle pull] {len(new_proved)} new remote candidates | lifetime {len(ledger)}",
            "\n".join(lines),
        )


if __name__ == "__main__":
    main()
