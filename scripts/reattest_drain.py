#!/usr/bin/env python3
"""reattest_drain.py — lazily migrate Brockian attestations to lean-4.32.2.

The 854 registry/attestations/*.json were generated at the now-deprecated lean-4.32.0.
This re-attests each module at the current env (engine.verify.DEFAULT_ENV = lean-4.32.2)
via scripts/attest.py, recording the env it was actually verified under. Resumable
(skips attestations already at the target env), capped (REATTEST_MAX), paced (AXLE_PACE).

Honesty rule — never silently downgrade: a module that was `module_verified` before but
FAILS at the new env is NOT overwritten; its regression is logged for human review, and
its old attestation is left in place. A module that re-verifies clean is written at the
new env. This keeps the registry honest during the migration instead of masking a
toolchain regression.

Run:  python3 scripts/reattest_drain.py            # writes verified re-attestations
      REATTEST_DRY_RUN=1 python3 scripts/reattest_drain.py   # report only, no writes
"""
from __future__ import annotations

import glob
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
import attest  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from engine.verify import DEFAULT_ENV  # noqa: E402

ATT_DIR = "registry/attestations"
MAX = int(os.environ.get("REATTEST_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))
DRY_RUN = os.environ.get("REATTEST_DRY_RUN") == "1"


def _source_path(att_json: str) -> str | None:
    """The attestation is named after the SOURCE FILE basename (its namespace may differ,
    e.g. Brockian/AdmissibilityCRT.lean declares namespace Brockian.Admissibility.CRT).
    Resolve the .lean by that stem under Brockian/."""
    stem = os.path.splitext(os.path.basename(att_json))[0]
    hits = (glob.glob(f"Brockian/{stem}.lean")
            + glob.glob(f"Brockian/**/{stem}.lean", recursive=True))
    return hits[0] if hits else None


def main() -> int:
    files = sorted(glob.glob(os.path.join(ATT_DIR, "*.json")))
    stale = []
    for f in files:
        try:
            att = json.load(open(f))
        except Exception:  # noqa: BLE001
            continue
        if att.get("environment") != DEFAULT_ENV:
            stale.append((f, att))
    todo = stale[:MAX]
    print(f"{len(files)} attestations; {len(stale)} not at {DEFAULT_ENV}; "
          f"re-attesting {len(todo)}{' (DRY RUN)' if DRY_RUN else ''}")

    migrated = regressed = skipped = 0
    for f, old in todo:
        module = old.get("module", "")
        src = _source_path(f)
        names = [d["name"].split(".")[-1] for d in old.get("declarations", [])]
        if not src or not names:
            skipped += 1
            print(f"  SKIP {os.path.basename(f)} (no source / no names)")
            continue
        try:
            new = attest.attest(src, module, names, DEFAULT_ENV)
        except Exception as e:  # noqa: BLE001
            skipped += 1
            print(f"  SKIP {os.path.basename(f)} (attest error: {str(e)[:80]})")
            time.sleep(PACE)
            continue
        was_verified = old.get("module_verified") is True
        # A clean module compile without a parsed per-declaration axiom report is an
        # incomplete attestation, not a successful migration.
        now_verified = attest.attestation_complete(new)
        if now_verified:
            if not DRY_RUN:
                json.dump(new, open(f, "w"), indent=2)
            migrated += 1
            print(f"  OK   {os.path.basename(f)} -> {DEFAULT_ENV}")
        elif was_verified:
            regressed += 1
            print(f"  REGRESSED {os.path.basename(f)}: verified@old, FAILS@{DEFAULT_ENV} "
                  f"— kept old attestation, needs review")
        else:
            # was not verified before and still isn't — write the honest new-env record
            if not DRY_RUN:
                json.dump(new, open(f, "w"), indent=2)
            migrated += 1
            print(f"  .. {os.path.basename(f)} (still unverified, recorded @ {DEFAULT_ENV})")
        time.sleep(PACE)

    print(f"\nre-attested {migrated} | regressed {regressed} | skipped {skipped} "
          f"| remaining stale {len(stale) - len(todo)}")
    return 1 if regressed else 0


if __name__ == "__main__":
    sys.exit(main())
