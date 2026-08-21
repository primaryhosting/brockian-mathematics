"""engine.audit — the single honesty gate.

Runs the three enforcers as ONE `--strict` surface:
  1. registry consistency  (scripts/audit_registry_consistency.py --strict) — the
     authoritative re-derivation of register invariants on the committed registry.
  2. overclaim firewall    (scripts/verify_firewall.py) — #35 overclaim + #36
     self-consistency over registry/theorems.json.
  3. no-theater lint       (scripts/no_theater_lint.py) — fake-proof line patterns;
     a sorry/admit in a CLAIMED module (one imported by Brockian.lean) is blocking.
  4. attestation integrity (scripts/check_attestation_integrity.py) — local, no-AXLE
     check that every attested declaration exists in its source with a matching kind
     (catches the attestation-gap class before a costly re-attestation).

This is what the conveyor's registry hop gates on. Previously the hop ran only surface 1,
so surfaces 2 and 3 were never enforced on the hop; folding them here enforces all three.
Each surface is run as a subprocess so its exact, battle-tested logic is preserved — this
module is the single ENTRY, not a re-implementation. Any hard finding fails `--strict`.
"""
from __future__ import annotations

import argparse
import glob
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PY = sys.executable
_IMPORT = re.compile(r"^import\s+(Brockian(?:\.[A-Za-z0-9_']+)+)")


def claimed_modules() -> set:
    """Short module names imported by Brockian.lean — the claimed corpus. A hole in one
    of these is an overclaim, so no_theater_lint treats them as closed (blocking)."""
    root = REPO / "Brockian.lean"
    out = set()
    if root.exists():
        for line in root.read_text(encoding="utf-8", errors="ignore").splitlines():
            m = _IMPORT.match(line.strip())
            if m:
                out.add(m.group(1).split(".")[-1])
    return out


def _run(cmd) -> tuple[int, str]:
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def run(strict: bool = True) -> list:
    """Run all three surfaces. Return [(name, ok, output_tail), ...]; ok=False = a hard
    finding on that surface."""
    results = []

    rc, out = _run([PY, "scripts/audit_registry_consistency.py"]
                   + (["--strict"] if strict else []))
    results.append(("registry-consistency", rc == 0, out))

    rc, out = _run([PY, "scripts/verify_firewall.py"])
    results.append(("overclaim-firewall", rc == 0, out))

    leans = sorted(glob.glob(str(REPO / "Brockian" / "**" / "*.lean"), recursive=True))
    closed = sorted(claimed_modules())
    if leans:
        rc, out = _run([PY, "scripts/no_theater_lint.py", *leans, "--closed", *closed])
    else:
        rc, out = 0, "no Brockian/*.lean found"
    results.append(("no-theater-lint", rc == 0, out))

    rc, out = _run([PY, "scripts/check_attestation_integrity.py"]
                   + (["--strict"] if strict else []))
    results.append(("attestation-integrity", rc == 0, out))

    return results


def main() -> int:
    ap = argparse.ArgumentParser(description="Unified honesty gate for the registry.")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 if any surface reports a hard finding")
    args = ap.parse_args()
    results = run(strict=args.strict)
    failed = [name for name, ok, _ in results if not ok]
    for name, ok, tail in results:
        print(f"[{'PASS' if ok else 'FAIL'}] {name}")
        if not ok:
            body = "\n  ".join(tail.strip().splitlines()[-8:])
            print(f"  {body}")
    passed = len(results) - len(failed)
    print(f"\nengine.audit: {passed}/{len(results)} surfaces pass"
          + (f"; FAILED: {failed}" if failed else ""))
    return 1 if (args.strict and failed) else 0


if __name__ == "__main__":
    sys.exit(main())
