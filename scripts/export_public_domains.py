#!/usr/bin/env python3
"""Export a SANITIZED public catalogue of Aristotle fleet domain proofs.

Honesty rules (hard, in code):
  * ALLOWLIST fields only: name, domain, register, statement, verified_by, env.
  * NO ENTRY SHIPS WITHOUT ITS ACTUAL LEAN STATEMENT TEXT, extracted from the
    committed proof file. Names in some tiers are aspirational labels
    (e.g. *.TwinPrimeConjecture proves a reduction, NOT the conjecture);
    the binding content is the statement. Entries whose statement cannot be
    extracted are EXCLUDED and counted in the exclusion report.
  * register PROVED only when verification == AXLE OK at our env; otherwise
    exported as UNVERIFIED (Aristotle-reported, not attested).
  * A top-level naming_caveat is embedded in the file itself.
Stdlib only. Run: python3 scripts/export_public_domains.py
"""
import json, os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IN = os.path.join(REPO, "registry", "domains.json")
OUT = os.path.join(REPO, "torus", "public", "verified-domains.json")
STMT_MAX = 420

src = json.load(open(IN))
out, excluded = [], []
for name, e in sorted(src.items()):
    if not isinstance(e, dict):
        excluded.append((name, "malformed")); continue
    pf = e.get("proof_file")
    stmt = e.get("statement")
    kind = None
    if not stmt and pf:
        path = os.path.join(REPO, pf)
        try:
            txt = open(path, encoding="utf-8", errors="replace").read()
            last = name.split(".")[-1]
            # Prefer a THEOREM named after the target; else the file's main theorem;
            # else a def (which is a STATEMENT formalization, never a proof).
            m = re.search(r"^(theorem|lemma)\s+" + re.escape(last) + r"\b(.*?):=", txt, re.S | re.M)
            if not m:
                m = re.search(r"^(theorem|lemma)\s+([\w.']+)\b(.*?):=", txt, re.S | re.M)
                if m:
                    kind = m.group(1)
                    stmt = re.sub(r"\s+", " ", (m.group(1) + " " + m.group(2) + m.group(3))).strip()
            else:
                kind = m.group(1)
                stmt = re.sub(r"\s+", " ", (m.group(1) + " " + last + m.group(2))).strip()
            if not stmt:
                m = re.search(r"^(def)\s+" + re.escape(last) + r"\b(.*?):=", txt, re.S | re.M) or                     re.search(r"^(def)\s+([\w.']+)\b(.*?):=", txt, re.S | re.M)
                if m:
                    kind = "def"
                    stmt = re.sub(r"\s+", " ", m.group(0)[:-2]).strip()
        except OSError:
            pass
    if not stmt:
        excluded.append((name, "no-statement")); continue
    ver = str(e.get("verification", ""))
    attested = "AXLE" in ver and "OK" in ver
    if kind == "def":
        register = "STATEMENT"   # a formalized definition, NOT a proof of anything
    elif attested:
        register = "PROVED"
    else:
        register = "UNVERIFIED"
    out.append({
        "name": name,
        "domain": e.get("domain", "?"),
        "register": register,
        "statement": stmt[:STMT_MAX],
        "verified_by": ("AXLE cloud" if attested else "Aristotle-reported only (NOT attested)") if kind != "def" else "n/a (statement definition, no proof content)",
        "env": "lean-4.32.0" if attested else None,
    })

doc = {
    "schema": "riemannlab-fleet-domains-v1",
    "generated_from": "registry/domains.json via scripts/export_public_domains.py (allowlist sanitizer)",
    "naming_caveat": ("Lean identifiers in this catalogue can be aspirational labels: a name like "
        "'TwinPrimeConjecture' may denominate a machine-verified REDUCTION or CONDITIONAL theorem, "
        "never a proof of the open problem unless the statement text says so. The binding content of "
        "every entry is its statement field. Open problems remain open."),
    "summary": {
        "total": len(out),
        "PROVED_attested": sum(1 for x in out if x["register"] == "PROVED"),
        "STATEMENT_only": sum(1 for x in out if x["register"] == "STATEMENT"),
        "UNVERIFIED": sum(1 for x in out if x["register"] == "UNVERIFIED"),
        "excluded_no_statement": len(excluded),
    },
    "entries": out,
}
os.makedirs(os.path.dirname(OUT), exist_ok=True)
json.dump(doc, open(OUT, "w"), ensure_ascii=False, indent=1)
print("exported", len(out), "entries ->", OUT)
print("summary:", doc["summary"])
print("excluded (first 10):", excluded[:10])
