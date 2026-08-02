"""validate_manifests.py — the honesty firewall at BUILD time (roadmap: torus).

The `<VerifiedClaim>` component enforces honesty at render time (an unbacked claim shows BLOCKED).
This enforces it earlier and harder: a lab manifest may not even be committed if any of its claims
cites a theorem the verified registry does not contain. CI-gateable — exit non-zero on any violation.

Rules per claim (theorem, register):
  - theorem MUST resolve in registry/theorems.json (fully-qualified name). Absent ⇒ FAIL.
  - register ∈ {PROVED, DISCHARGED, DEFINITION}         ⇒ OK   (a green certificate is honest)
  - register ∈ {CONDITIONAL, CONJECTURE}                ⇒ WARN (the component will render it as a
        non-green open state — allowed, but the lab author is told it is NOT a verified badge)
  - register == UNVERIFIED / anything else              ⇒ FAIL

Also checks manifest shape (labId pattern, required fields) so a malformed manifest fails loudly.
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys

REGISTRY = "registry/theorems.json"
LABS_GLOB = "torus/labs/*.manifest.json"
GREEN = {"PROVED", "DISCHARGED", "DEFINITION"}
OPEN = {"CONDITIONAL", "CONJECTURE"}
LABID_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")


def load_registry() -> dict[str, str]:
    if not os.path.exists(REGISTRY):
        print(f"FATAL: {REGISTRY} not found", file=sys.stderr)
        sys.exit(2)
    d = json.load(open(REGISTRY))
    return {t["name"]: t["register"] for t in d.get("theorems", [])}


def validate(path: str, reg: dict[str, str]) -> tuple[list[str], list[str], int]:
    errs: list[str] = []
    warns: list[str] = []
    try:
        m = json.load(open(path))
    except Exception as e:
        return [f"{path}: invalid JSON — {e}"], [], 0
    lab = m.get("labId", "?")
    if not isinstance(lab, str) or not LABID_RE.match(lab or ""):
        errs.append(f"{path}: labId {lab!r} does not match ^[a-z0-9][a-z0-9-]*$")
    claims = m.get("claims")
    if not isinstance(claims, list) or not claims:
        errs.append(f"{path}: 'claims' must be a non-empty array")
        return errs, warns, 0
    for i, c in enumerate(claims):
        where = f"{lab}[{i}]"
        if not isinstance(c, dict) or "claim" not in c or "theorem" not in c:
            errs.append(f"{where}: each claim needs 'claim' and 'theorem'")
            continue
        thm = c["theorem"]
        if thm not in reg:
            errs.append(f"{where}: theorem NOT in registry — {thm!r}  (claim: {c['claim'][:60]!r})")
            continue
        r = reg[thm]
        if r in OPEN:
            warns.append(f"{where}: {thm} is {r} — renders as an OPEN (non-verified) state, not a green badge")
        elif r not in GREEN:
            errs.append(f"{where}: {thm} has register {r} — not fit to back a claim")
    return errs, warns, len(claims)


def main() -> int:
    reg = load_registry()
    manifests = sorted(glob.glob(LABS_GLOB))
    if not manifests:
        print(f"no lab manifests under {LABS_GLOB} (nothing to validate)")
        return 0
    all_err: list[str] = []
    all_warn: list[str] = []
    total_claims = 0
    print(f"validating {len(manifests)} lab manifest(s) against {len(reg)} registry theorems\n")
    for p in manifests:
        e, w, n = validate(p, reg)
        total_claims += n
        all_err += e
        all_warn += w
        status = "FAIL" if e else ("warn" if w else "OK")
        print(f"  [{status}] {os.path.basename(p)} — {n} claim(s)"
              + (f", {len(e)} error(s)" if e else "")
              + (f", {len(w)} warning(s)" if w else ""))
    print()
    for w in all_warn:
        print("  WARN " + w)
    for e in all_err:
        print("  ERR  " + e)
    print()
    if all_err:
        print(f"FIREWALL: {len(all_err)} violation(s) across {len(manifests)} manifest(s) — "
              f"a lab cites a claim the verified core does not back.")
        return 1
    print(f"CLEAN — all {total_claims} claim(s) across {len(manifests)} lab(s) resolve to backed registry theorems"
          + (f" ({len(all_warn)} render as honest open states)" if all_warn else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
