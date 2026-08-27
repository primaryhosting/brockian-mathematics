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
  * when a receipt has ``content_hash``, it equals the canonical flattened source hash;
  * newly changed receipts, and receipts for newly changed Lean modules, carry that hash.

Run:  python3 scripts/check_attestation_integrity.py [--strict]
      python3 scripts/check_attestation_integrity.py --strict \
        --require-content-hash-for-changed <base-commit>
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
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


def _required_hash_paths(changed_paths: list[str]) -> set[str]:
    """Map a git diff to attestation receipts that must use the hashed schema.

    Existing legacy receipts are grandfathered until either the receipt itself or its
    corresponding Lean source changes.  A source with no attestation is ignored because
    it contributes nothing to the registry.
    """
    required: set[str] = set()
    for changed in changed_paths:
        path = changed.replace("\\", "/")
        if path.startswith(f"{ATT_DIR}/") and path.endswith(".json"):
            required.add(path)
            continue
        if not (path.startswith("Brockian/") and path.endswith(".lean")):
            continue
        stem = os.path.splitext(os.path.basename(path))[0]
        receipt = f"{ATT_DIR}/{stem}.json"
        if os.path.exists(receipt):
            required.add(receipt)
    return required


def _git_changed_paths(base: str) -> list[str]:
    result = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, "HEAD", "--",
         "Brockian", ATT_DIR],
        check=True,
        capture_output=True,
        text=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def check(required_hash_paths: set[str] | None = None) -> list[tuple[str, str]]:
    """Return a list of (level, message). level in {'ERROR'}."""
    findings: list[tuple[str, str]] = []
    required_hash_paths = required_hash_paths or set()
    hash_cache: dict[str, str] = {}
    for f in sorted(glob.glob(os.path.join(ATT_DIR, "*.json"))):
        relative_attestation = f.replace("\\", "/")
        try:
            att = json.load(open(f))
        except Exception as e:  # noqa: BLE001
            findings.append(("ERROR", f"{os.path.basename(f)}: unreadable ({e})"))
            continue
        src_path = _source_path(f)
        recorded_hash = att.get("content_hash")
        if relative_attestation in required_hash_paths and not recorded_hash:
            findings.append(("ERROR",
                f"{os.path.basename(f)}: changed receipt/source lacks content_hash "
                f"(attestation-content-hash-missing)"))
        if recorded_hash is not None:
            if not src_path:
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: hashed receipt has no source "
                    f"(attestation-source-missing)"))
            elif not isinstance(recorded_hash, str):
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: content_hash is not a string "
                    f"(attestation-content-hash-invalid)"))
            else:
                if src_path not in hash_cache:
                    hash_cache[src_path] = attest.content_hash(attest._flatten(src_path))
                expected_hash = hash_cache[src_path]
                if recorded_hash != expected_hash:
                    findings.append(("ERROR",
                        f"{os.path.basename(f)}: content_hash {recorded_hash!r} != "
                        f"source {expected_hash!r} (attestation-content-hash-mismatch)"))
        if not src_path:
            continue  # orphan attestation without local source — not this check's job
        src = open(src_path, encoding="utf-8").read()
        for d in att.get("declarations", []):
            short = d.get("name", "").split(".")[-1]
            if not short:
                continue
            recorded_kind = d.get("kind", "theorem")
            quarantined = d.get("verification_quarantine") is True
            if _class_of(recorded_kind) == "proof" and not quarantined:
                raw_axioms = d.get("axioms")
                if not isinstance(raw_axioms, list):
                    findings.append(("ERROR",
                        f"{os.path.basename(f)}: '{short}' lacks a parsed axiom list "
                        f"(attestation-axiom-report-missing)"))
                elif not set(raw_axioms).issubset(attest.ALLOWED):
                    findings.append(("ERROR",
                        f"{os.path.basename(f)}: '{short}' has disallowed axioms "
                        f"(attestation-axioms-not-allowed)"))
                if d.get("axioms_ok") is not True:
                    findings.append(("ERROR",
                        f"{os.path.basename(f)}: '{short}' axioms_ok is not true "
                        f"(attestation-axioms-not-ok)"))
                if d.get("axle_verdict") != "verified":
                    findings.append(("ERROR",
                        f"{os.path.basename(f)}: '{short}' lacks a verified AXLE verdict "
                        f"(attestation-declaration-unverified)"))
            if not _declared(src, short):
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: '{short}' not declared in {src_path} "
                    f"(attestation-name-missing)"))
                continue
            src_kind = attest._kind_of(src, short)
            if _class_of(recorded_kind) != _class_of(src_kind):
                findings.append(("ERROR",
                    f"{os.path.basename(f)}: '{short}' attested as {recorded_kind} but "
                    f"source is {src_kind} (attestation-kind-mismatch)"))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description="Local attestation↔source integrity gate.")
    ap.add_argument("--strict", action="store_true", help="exit 1 on any ERROR")
    ap.add_argument(
        "--require-content-hash-for-changed",
        metavar="BASE",
        help=("require the hashed schema for receipts or corresponding Lean modules "
              "changed since BASE"),
    )
    args = ap.parse_args()
    required: set[str] = set()
    if args.require_content_hash_for_changed:
        try:
            required = _required_hash_paths(
                _git_changed_paths(args.require_content_hash_for_changed))
        except subprocess.CalledProcessError as exc:
            print(f"[ERROR] cannot compute changed attestation set: {exc}")
            return 1
    findings = check(required)
    for level, msg in findings[:200]:
        print(f"[{level}] {msg}")
    errors = sum(1 for lvl, _ in findings if lvl == "ERROR")
    total = len(glob.glob(os.path.join(ATT_DIR, "*.json")))
    print(f"\nattestation integrity: {total} attestations checked | {errors} errors | "
          f"{len(required)} changed receipts hash-required")
    return 1 if (args.strict and errors) else 0


if __name__ == "__main__":
    sys.exit(main())
