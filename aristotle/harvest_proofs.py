#!/usr/bin/env python3
"""Download terminal Aristotle jobs tracked in ``submitted_night.json``.

``PROVED`` in the ledger is the remote service verdict only.  It is never described
as a compile certificate or as axiom-clean; local Lean/AXLE and a saved axiom report
are separate downstream gates.
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
except ModuleNotFoundError:  # imported as ``aristotle.harvest_proofs`` in tests/tools
    from .proof_identity import identity_metadata

ROOT = pathlib.Path(__file__).resolve().parent
NIGHT = ROOT / "submitted_night.json"
OUT = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
REPORT = ROOT / "harvest_report.md"
NOTIFY = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")
KEYENV = {"admin": "ARISTOTLE_API_KEY", "chris": "ARISTOTLE_API_KEY_CHRIS"}
MAX = int(os.environ.get("HARVEST_MAX", "60"))
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")


def run(args, key, timeout=180):
    env = dict(os.environ)
    if key:
        env["ARISTOTLE_API_KEY"] = key
    try:
        process = subprocess.run(
            ["uvx", "--from", "aristotlelib@latest", "aristotle", *args],
            capture_output=True,
            text=True,
            env=env,
            timeout=timeout,
        )
        return (process.stdout or "") + (process.stderr or "")
    except Exception:  # noqa: BLE001
        return ""


def fetch(project_id, key):
    directory = tempfile.mkdtemp(prefix="harv_")
    archive = os.path.join(directory, f"{project_id}.tar.gz")
    try:
        run(["download", project_id, "--destination", archive], key)
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


def night_job_ids(night):
    return {
        record["project_id"]
        for value in night.values()
        for record in value.get("ids", [])
        if record.get("project_id")
    }


def main():
    OUT.mkdir(exist_ok=True)
    night = json.loads(NIGHT.read_text()) if NIGHT.exists() else {}
    harvested = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}

    jobs = []
    for target, value in night.items():
        for record in value.get("ids", []):
            project_id = record["project_id"]
            if project_id not in harvested:
                jobs.append((target, record["account"], project_id, value.get("tier")))

    newly = []
    for target, account, project_id, tier in jobs[:MAX]:
        key = os.environ.get(KEYENV.get(account, ""))
        if not key:
            continue
        terminal, verdict, lean = fetch(project_id, key)
        if not terminal:
            continue

        record = {
            "target": target,
            "account": account,
            "verdict": verdict,
            "tier": tier,
            "verification_status": (
                "remote_candidate_static_placeholder_scan" if verdict == "PROVED" else "remote_stopped"
            ),
        }
        if verdict == "PROVED":
            filename = f"{account}_{project_id}.lean"
            (OUT / filename).write_text(lean)
            record["source_file"] = filename
            record.update(identity_metadata(lean))
        harvested[project_id] = record
        newly.append((target, account, verdict, project_id))
        LEDGER.write_text(json.dumps(harvested, indent=1))

    remote_proved = [item for item in harvested.values() if item.get("verdict") == "PROVED"]
    ids = night_job_ids(night)
    resolved_ids = ids.intersection(harvested)
    unresolved_ids = ids.difference(harvested)
    foreign_terminal = set(harvested).difference(ids)
    stopped = len(harvested) - len(remote_proved)
    lines = [
        "# Aristotle harvest",
        f"- current submission ledger resolved: {len(resolved_ids)}/{len(ids)}",
        f"- current submission ledger still nonterminal: {len(unresolved_ids)}",
        f"- lifetime terminal records: {len(harvested)}",
        f"- terminal records outside current submission ledger: {len(foreign_terminal)}",
        f"- remote PROVED candidates (pending local Lean/AXLE): {len(remote_proved)}",
        f"- STOPPED/static-placeholder records: {stopped}",
        "",
        "## Remote PROVED candidates",
    ]
    for item in sorted(remote_proved, key=lambda value: value["target"]):
        lines.append(f"- [{item.get('tier')}] {item['target']} ({item['account']})")
    REPORT.write_text("\n".join(lines) + "\n")

    if newly:
        new_proved = sum(1 for _, _, verdict, _ in newly if verdict == "PROVED")
        subject = (
            f"[harvest] {new_proved} new remote proof candidates | "
            f"night {len(resolved_ids)}/{len(ids)} | lifetime {len(harvested)}"
        )
        body = [
            f"newly terminal {len(newly)} ({new_proved} remote PROVED candidates)",
            f"lifetime remote PROVED candidates {len(remote_proved)}",
            "Remote status is not local/AXLE verification and is not an axiom report.",
            "",
        ]
        body.extend(
            f"  {verdict} {target} ({account}) {project_id}"
            for target, account, verdict, project_id in newly
        )
        email(subject, "\n".join(body))

    print(
        f"harvested {len(newly)} this run | night {len(resolved_ids)}/{len(ids)} | "
        f"lifetime {len(harvested)} ({len(remote_proved)} remote PROVED candidates)"
    )


if __name__ == "__main__":
    main()
