"""Produce an AXLE verification attestation for a Brockian module.

Reads a .lean module, appends `#print axioms` probes for the named declarations, runs
AXLE `check` at the given environment, and writes registry/attestations/<Module>.json
recording the independent verdict + axiom set per declaration (spec §2A / §5).

Usage:
    python3 scripts/attest.py Brockian/GoldbachComb.lean Brockian.GoldbachComb \
        gCount_eq gCount_centered local_covariance [--env lean-4.32.0]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import axle_client  # noqa: E402

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def _kind_of(src: str, name: str) -> str:
    """Detect a declaration's kind from the source (theorem/lemma vs def/abbrev)."""
    if re.search(rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:theorem|lemma)\s+{re.escape(name)}\b",
                 src, re.MULTILINE):
        return "theorem"
    m = re.search(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev)\s+{re.escape(name)}\b(.*?):=",
        src, re.MULTILINE | re.DOTALL)
    if m:
        # a Prop-typed def is a conjecture container; any other def is a supporting definition
        return "conjecture" if re.search(r":\s*Prop\b", m.group(1)) else "def"
    return "theorem"


def attest(lean_path: str, namespace: str, names: list[str], env: str) -> dict:
    src = open(lean_path, encoding="utf-8").read()
    probe = src + "\n" + "\n".join(
        f"open {namespace} in\n#print axioms {n}" for n in names
    ) + "\n"
    r = axle_client.check(probe, env=env, timeout=300)
    infos = (r.raw.get("lean_messages") or {}).get("infos", [])

    def axioms_for(n: str) -> list[str] | None:
        needle = f"{namespace}.{n}'"
        for i in infos:
            s = i if isinstance(i, str) else str(i)
            if needle in s and "axioms" in s:
                m = re.search(r"\[([^\]]*)\]", s)
                return [a.strip() for a in m.group(1).split(",")] if m else []
        return None

    decls = []
    for n in names:
        ax = axioms_for(n)
        decls.append({
            "name": f"{namespace}.{n}",
            "kind": _kind_of(src, n),
            "axle_verdict": "verified" if r.verified else "failed",
            "axioms": ax,
            "axioms_ok": (ax is not None and set(ax).issubset(ALLOWED)),
        })
    return {
        "module": namespace,
        "environment": r.environment,
        "module_verified": r.verified,
        "declarations": decls,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("lean_path")
    ap.add_argument("namespace")
    ap.add_argument("names", nargs="+")
    ap.add_argument("--env", default="lean-4.32.0")
    args = ap.parse_args()
    att = attest(args.lean_path, args.namespace, args.names, args.env)
    out = os.path.join("registry", "attestations", args.namespace.split(".")[-1] + ".json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    json.dump(att, open(out, "w"), indent=2)
    print(json.dumps(att, indent=2))
    return 0 if att["module_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
