#!/usr/bin/env python3
"""Compile the structural review targets and preserve exact local-kernel evidence.

This check does not replace the promotion gate or manufacture AXLE attestations.
Every theorem in each successfully compiled structural module is probed. A missing
or unparseable axiom report fails the audit. Sources are compiled as committed;
imports are never normalized by this checker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from check_lean_modules import dependency_order
from engine.verify import ALLOWED_AXIOMS, axioms_in_line, qualified_decls

TARGETS = [
    "Brockian/FrickeChannelAlgebra.lean",
    "Brockian/CyclicFourierStructure.lean",
    "Brockian/HolonomyObservers.lean",
    "Brockian/HodgeGramAlgebra.lean",
    "Brockian/QCQFTUnitary.lean",
    "Brockian/OddPerfectThreePrimes.lean",
    "Brockian/SieveSpectrumCounts.lean",
    "Brockian/SieveSpectrumBlocks.lean",
    "Brockian/SieveSpectrumDeletion.lean",
]
STRUCTURAL = {"Brockian/FrickeChannelAlgebra.lean", "Brockian/CyclicFourierStructure.lean",
              "Brockian/QCQFTUnitary.lean", "Brockian/HolonomyObservers.lean",
              "Brockian/HodgeGramAlgebra.lean"}
WEYL = ["Brockian/ConfiningSpectralShape.lean", "Brockian/WeylWeakRegularityClosed.lean",
        "Brockian/WeylWeakRegularityDischarge.lean", "Brockian/WeylKatoRellichTransfer.lean"]


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--group", choices=["structural", "weyl"], default="structural")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    version = run(["lake", "env", "lean", "--version"])
    commit = run(["git", "rev-parse", "HEAD"])
    receipt = {
        "schema_version": 1,
        "group": args.group,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "source_commit": commit.stdout.strip(),
        "lean_version": version.stdout.strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
        "verification_scope": "Lean kernel compilation and complete per-module theorem axiom probes",
        "external_attestation": "not_performed",
        "modules": [],
    }
    failed = version.returncode != 0
    targets = TARGETS if args.group == "structural" else WEYL
    for source in dependency_order([ROOT / p for p in targets], ROOT):
        rel = source.relative_to(ROOT).as_posix()
        mod = rel.removesuffix(".lean").replace("/", ".")
        dest = ROOT / ".lake/build/lib/lean" / Path(rel).with_suffix(".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        command = ["lake", "env", "lean", "-o", str(dest), rel]
        print(f"Compiling {rel}", flush=True)
        result = run(command)
        (out / f"{mod}.build.log").write_text(result.stdout)
        record = {"path": rel, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "command": command, "exit_code": result.returncode,
                  "compiled": result.returncode == 0, "theorems": []}
        bad = result.returncode != 0 or bool(re.search(r"declaration uses ['`]sorry", result.stdout))
        if rel in STRUCTURAL and not bad:
            names = qualified_decls(source.read_text())
            probe = out / f"{mod}.axioms.lean"
            probe.write_text(f"import {mod}\n" +
                             "\n".join(f"#print axioms {n}" for n in names) + "\n")
            checked = run(["lake", "env", "lean", str(probe)])
            (out / f"{mod}.axioms.log").write_text(checked.stdout)
            bad |= checked.returncode != 0 or not names
            for name in names:
                pattern = rf"'{re.escape(name)}' (?:does not depend on any axioms|depends on axioms:\s*\[[^\]]*\])"
                matches = re.findall(pattern, checked.stdout, flags=re.DOTALL)
                ax = axioms_in_line(matches[0]) if len(matches) == 1 else None
                okay = ax is not None and set(ax).issubset(ALLOWED_AXIOMS)
                record["theorems"].append({"name": name, "axioms": ax, "axioms_ok": okay})
                bad |= not okay
        record["audit_passed"] = not bad
        receipt["modules"].append(record)
        failed |= bad
        print(result.stdout[-12000:], flush=True)
        print(f"{rel}: {'FAIL' if bad else 'PASS'}", flush=True)
    receipt["passed"] = not failed
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"passed": not failed, "modules": len(receipt["modules"])}), flush=True)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
