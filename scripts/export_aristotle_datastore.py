#!/usr/bin/env python3
"""Export the FULL Aristotle-harvest proof corpus as a single datastore for the Riemann lab.

Unlike export_public_domains.py (a sanitized metadata catalogue), this emits every deduped
best_proof with its SOURCE and its exact, per-proof verification tier — a queryable store
of the actual proofs, honestly labeled. It joins:
  aristotle/best_proofs/*.lean  (the proof source, deduped)
  registry/domains.json          (domain / register / provenance / statement)
  aristotle/axle_verify.json     (AXLE cloud compile verdict + environment)
  aristotle/axle_axiom_audit.json(AXLE cloud axiom audit: kernel-clean?)

Honesty (hard rules, in code):
  * Every proof carries a `tier`, never a bare "proved":
      AXLE_VERIFIED_AXIOM_CLEAN — AXLE compiled AND axiom-audited kernel-clean (the only
                                  tier the registry counts as PROVED), env recorded.
      AXLE_VERIFIED             — AXLE compiled, axiom audit not (yet) clean/available.
      ARISTOTLE_CANDIDATE       — Aristotle self-reported only; NOT independently verified.
  * A prominent top-level honesty note; counts split by tier; naming_caveat retained.
  * All three verdicts are hash-gated: a verdict only counts if it matches THIS proof's
    content hash (so a stale verdict for an edited proof is dropped to the lower tier).

Output: torus/public/aristotle-datastore.json  (a deploy artifact; git-ignored).
Stdlib only.  Run:  python3 scripts/export_aristotle_datastore.py
"""
import glob
import hashlib
import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BEST = os.path.join(REPO, "aristotle", "best_proofs")
DOMAINS = os.path.join(REPO, "registry", "domains.json")
AXLE = os.path.join(REPO, "aristotle", "axle_verify.json")
AUDIT = os.path.join(REPO, "aristotle", "axle_axiom_audit.json")
OUT = os.path.join(REPO, "torus", "public", "aristotle-datastore.json")
ENV = "lean-4.32.2"
STMT_MAX = 600
_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:theorem|lemma)\s+"
                   r"([A-Za-z_][\w'.]*)\s*(.*?)(?::=|\bby\b|$)", re.S)


def _load(p):
    try:
        return json.load(open(p))
    except Exception:  # noqa: BLE001
        return {}


def normalize(content: str) -> str:
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    return "\n".join(imports + [""] + body)


def content_hash(content: str) -> str:
    return hashlib.sha256(normalize(content).encode()).hexdigest()[:16]


def statement_of(src: str) -> str | None:
    """First theorem/lemma statement text (name + signature), trimmed."""
    m = _DECL.search(normalize(src))
    if not m:
        return None
    stmt = f"{m.group(1)} {m.group(2)}".strip()
    stmt = re.sub(r"\s+", " ", stmt)
    return stmt[:STMT_MAX]


def main() -> int:
    domains = _load(DOMAINS)
    axle = _load(AXLE)
    audit = _load(AUDIT)
    # domains is keyed by target name; build a filename->entry map via sanitized target
    dom_by_file = {}
    for target, e in domains.items():
        if isinstance(e, dict):
            fn = re.sub(r"[^A-Za-z0-9]+", "_", target) + ".lean"
            dom_by_file[fn] = (target, e)

    entries = []
    counts = {"AXLE_VERIFIED_AXIOM_CLEAN": 0, "AXLE_VERIFIED": 0, "ARISTOTLE_CANDIDATE": 0}
    for f in sorted(glob.glob(os.path.join(BEST, "*.lean"))):
        fn = os.path.basename(f)
        src = open(f, encoding="utf-8", errors="ignore").read()
        h = content_hash(src)
        av = axle.get(fn, {})
        au = audit.get(fn, {})
        verified = (av.get("verified") is True and av.get("environment") == ENV
                    and av.get("hash") == h)
        clean = (au.get("trusted") is True and au.get("environment") == ENV
                 and au.get("hash") == h)
        if verified and clean:
            tier = "AXLE_VERIFIED_AXIOM_CLEAN"
        elif verified:
            tier = "AXLE_VERIFIED"
        else:
            tier = "ARISTOTLE_CANDIDATE"
        counts[tier] += 1
        target, dmeta = dom_by_file.get(fn, (fn[:-5], {}))
        entries.append({
            "id": fn[:-5],
            "target": target,
            "domain": dmeta.get("domain"),
            "register": dmeta.get("register"),
            "statement": dmeta.get("statement") or statement_of(src),
            "tier": tier,
            "axle_verified": verified,
            "axiom_audit_clean": clean,
            "axioms": (au.get("axioms") if clean else None),
            "environment": ENV if verified else None,
            "provenance": dmeta.get("provenance"),
            "content_hash": h,
            "source": src,
        })

    store = {
        "_generated_by": "scripts/export_aristotle_datastore.py",
        "_honesty_note": (
            "Aristotle-harvest proof corpus. Each proof carries a `tier`: "
            "AXLE_VERIFIED_AXIOM_CLEAN = independently AXLE-compiled AND axiom-audited "
            "kernel-clean (the only tier counted PROVED); AXLE_VERIFIED = compiled, axiom "
            "audit not clean/available; ARISTOTLE_CANDIDATE = Aristotle self-reported only, "
            "NOT independently verified. A tier is never claimed unless its verdict matches "
            "the proof's content hash."),
        "naming_caveat": (
            "Some targets are aspirational labels (e.g. *.TwinPrimeConjecture proves a "
            "reduction, not the conjecture). The binding content is the `statement`."),
        "environment": ENV,
        "count": len(entries),
        "counts_by_tier": counts,
        "proofs": entries,
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(store, fh, indent=1)
    size_mb = os.path.getsize(OUT) / 1e6
    print(f"wrote {OUT} — {len(entries)} proofs, {size_mb:.1f} MB")
    print(f"tiers: {counts}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
