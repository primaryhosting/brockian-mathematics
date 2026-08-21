#!/usr/bin/env python3
"""check_attestation_integrity.py — local (no-AXLE) integrity gate over the attestations.

Catches the class of attestation-gap defect that surfaced in the lean-4.32.2 migration
WITHOUT paying for a full re-attestation: for every attestation declaration, confirm the
declaration actually exists in its source module and that its recorded kind matches the
source. A kind mismatch — an attestation calling `def Namespace.foo` a "theorem" — is
exactly what made the axiom probe address a non-proof-term and fail. This is fast and
local, so it can gate every registry hop and flag the defect before it costs an AXLE run.

Checks per attestation declaration `{module}.{short}` with recorded kind K:
  * the short name is declared in the source module (else attestation-name-missing);
  * the source's kind class agrees with K (else attestation-kind-mismatch), where
    "theorem"/"lemma" is one class and "def"/"abbrev"/"structure"/"class"/"inductive"/
    "conjecture" the other.

Run:  python3 scripts/check_attestation_integrity.py [--strict]   # exit 1 on any error
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import attest  # noqa: E402 — reuse the source declaration classifier

ATT_DIR = "registry/attestations"


def _source_path(att_json: str) -> str | None:
    stem = os.path.splitext(os.path.basename(att_json))[0]
    hits = (glob.glob(f"Brockian/{stem}.lean")
            + glob.glob(f"Brockian/**/{stem}.lean", recursive=True))
    return hits[0] if hits else None


def _declared(src: str, short: str) -> bool:
    """Is `short` declared in the source (bare or namespace-prefixed)?"""
    ident = re.escape(short) + r"(?![\w.'])"
    kw = r"theorem|lemma|def|abbrev|structure|class|inductive|instance"
    pat = (rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+)*"
           rf"(?:{kw})\s+(?:[\w'.]*\.)?{ident}")
    return re.search(pat, src, re.MULTILINE) is not None


def _class_of(kind: str) -> str:
    return "proof" if kind in ("theorem", "lemma") else "data"


def check() -> list[tuple[str, str]]:
    """Return a list of (level, message). level in {'ERROR'}."""
    findings: list[tuple[str, str]] = []
    for f in sorted(glob.glob(os.path.join(ATT_DIR, "*.json"))):
        try:
            att = json.load(open(f))
        except Exception as e:  # noqa: BLE001
            findings.append(("ERROR", f"{os.path.basename(f)}: unreadable ({e})"))
            continue
        src_path = _source_path(f)
        if not src_path:
            continue  # orphan attestation without local source — not this check's job
        src = open(src_path, encoding="utf-8").read()
        for d in att.get("declarations", []):
            short = d.get("name", "").split(".")[-1]
            if not short:
                continue
            if not _declared(src, short):
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: '{short}' not declared in {src_path} "
                    f"(attestation-name-missing)"))
                continue
            src_kind = attest._kind_of(src, short)
            if _class_of(d.get("kind", "theorem")) != _class_of(src_kind):
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: '{short}' attested as {d.get('kind')} but "
                    f"source is {src_kind} (attestation-kind-mismatch)"))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description="Local attestation↔source integrity gate.")
    ap.add_argument("--strict", action="store_true", help="exit 1 on any ERROR")
    args = ap.parse_args()
    findings = check()
    for level, msg in findings[:200]:
        print(f"[{level}] {msg}")
    errors = sum(1 for lvl, _ in findings if lvl == "ERROR")
    total = len(glob.glob(os.path.join(ATT_DIR, "*.json")))
    print(f"\nattestation integrity: {total} attestations checked | {errors} errors")
    return 1 if (args.strict and errors) else 0


if __name__ == "__main__":
    sys.exit(main())
