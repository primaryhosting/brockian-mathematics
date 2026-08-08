#!/usr/bin/env python3
"""Fetch the first 100k zeta-zero imaginary parts from Odlyzko's published
tables, verify, and emit datasets/zeta-zeros-100k.f64 (+ provenance sidecar).

Zero computation deliberately stays OFF this machine: we download published
values and cross-check them two ways (published literature values for the
first 10, mpmath for the first 100 -- seconds of work).
"""
import datetime
import hashlib
import json
import struct
import sys
import urllib.request
from pathlib import Path

SOURCE_URL = "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1"
EXPECTED_COUNT = 100_000
FIRST_ZERO = 14.134725141734693
OUT_DIR = Path(__file__).resolve().parent.parent / "datasets"
SPOT_CHECK_N = 100
SPOT_CHECK_TOL = 1e-8  # source is accurate to ~3e-9; 1e-9 unachievable (documented deviation)
# Second independent source (spec §4.3): first 10 zeros as published in the
# literature / LMFDB, to full double precision.
KNOWN_FIRST_TEN = [
    14.134725141734693, 21.022039638771554, 25.010857580145688,
    30.424876125859513, 32.935061587739189, 37.586178158825671,
    40.918719012147495, 43.327073280914999, 48.005150881167159,
    49.773832477672302,
]


def parse_zeros_text(text: str) -> list[float]:
    return [float(line) for line in text.splitlines() if line.strip()]


def validate_zeros(zeros: list[float], expected_count: int) -> None:
    if len(zeros) != expected_count:
        raise ValueError(f"expected {expected_count} zeros, got {len(zeros)}")
    if abs(zeros[0] - FIRST_ZERO) > 1e-6:
        raise ValueError(f"first zero {zeros[0]} != {FIRST_ZERO}")
    for i in range(1, len(zeros)):
        if zeros[i] <= zeros[i - 1]:
            raise ValueError(f"zeros not strictly increasing at index {i}")


def encode_f64le(zeros: list[float]) -> bytes:
    return struct.pack(f"<{len(zeros)}d", *zeros)


def spot_check_literature(zeros: list[float], tol: float) -> float:
    worst = max(abs(a - b) for a, b in zip(KNOWN_FIRST_TEN, zeros))
    if worst > tol:
        raise ValueError(f"literature spot-check failed: worst diff {worst} > {tol}")
    return worst


def spot_check_mpmath(zeros: list[float], n: int, tol: float) -> float:
    from mpmath import mp, zetazero
    mp.dps = 20
    worst = 0.0
    for k in range(1, n + 1):
        ref = float(zetazero(k).imag)
        worst = max(worst, abs(ref - zeros[k - 1]))
    if worst > tol:
        raise ValueError(f"mpmath spot-check failed: worst diff {worst} > {tol}")
    return worst


def _git_rev() -> str:
    try:
        import subprocess
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"], capture_output=True,
            text=True, cwd=Path(__file__).parent, timeout=10,
        ).stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def main() -> int:
    print(f"downloading {SOURCE_URL} ...")
    text = urllib.request.urlopen(SOURCE_URL, timeout=120).read().decode()
    zeros = parse_zeros_text(text)
    validate_zeros(zeros, EXPECTED_COUNT)
    worst_lit = spot_check_literature(zeros, SPOT_CHECK_TOL)
    print(f"literature spot-check OK (first 10, worst diff {worst_lit:.2e})")
    worst = spot_check_mpmath(zeros, SPOT_CHECK_N, SPOT_CHECK_TOL)
    print(f"mpmath spot-check OK (first {SPOT_CHECK_N}, worst diff {worst:.2e})")

    blob = encode_f64le(zeros)
    sha = hashlib.sha256(blob).hexdigest()
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "zeta-zeros-100k.f64").write_bytes(blob)
    provenance = {
        "dataset": "zeta-zeros-100k.f64",
        "content": "imaginary parts of the first 100000 nontrivial zeta zeros",
        "format": "float64 little-endian, strictly increasing",
        "count": EXPECTED_COUNT,
        "sha256": sha,
        "source_url": SOURCE_URL,
        "source_accuracy": "~3e-9 (per Odlyzko's table notes)",
        "retrieved_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "cross_checks": [
            {"method": "published literature/LMFDB values, first 10 zeros",
             "tolerance": SPOT_CHECK_TOL, "worst_diff": worst_lit},
            {"method": f"mpmath zetazero(1..{SPOT_CHECK_N}) at dps=20",
             "tolerance": SPOT_CHECK_TOL, "worst_diff": worst},
        ],
        "tolerance_note": "spec asked 1e-9; source accuracy is ~3e-9, so 1e-8 is the honest achievable bound",
        "generator": f"scripts/fetch_zeta_zeros.py@{_git_rev()}",
    }
    (OUT_DIR / "zeta-zeros-100k.provenance.json").write_text(
        json.dumps(provenance, indent=2))
    print(f"wrote {len(blob)} bytes, sha256={sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
