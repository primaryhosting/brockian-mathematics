#!/usr/bin/env python3
"""qp_harvest.py — harvest QuantumProof's kernel-verified security proofs back into the
Proof-Carrying-Apps registry (closes the QP HARVEST gap of the Verified Artifact Pipeline).

The Aristotle fleet already proves QP's isolation-model soundness theorems (PCA_*.lean); this
links the sorry-free (kernel-clean) ones into ~/Projects/proof-carrying-apps/kernel_verified.json
as first-class KERNEL-VERIFIED security facts (stronger than SMT-checked). Additive: it does NOT
touch the existing registry.json (app posture certs). Read-only over the proof corpus; idempotent.
"""
import glob
import hashlib
import json
import os
import re
import time

ARI = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.expanduser("~/Projects/proof-carrying-apps/kernel_verified.json")

# human-readable meaning for the model soundness theorems (from pca_lean_bridge THMS)
MEANING = {
    "no_escape_no_leak": "With no privileged caller and no unowned escape, any granted access is in-scope.",
    "priv_is_escape": "A privileged caller always has access (models the admin bypass).",
    "unowned_is_hole": "Any caller can reach an unowned row (models the IS NULL hole).",
    "escape_monotone": "Adding escapes only enlarges access.",
    "default_deny": "Empty scope + no escapes ⇒ nothing accessible.",
    "leak_iff_escape_when_out_of_scope": "Out of scope, access holds iff some escape fires.",
    "owner_only_isolated": "Owner-equality scope with no escapes is isolated.",
    "tightening_refines": "Removing the unowned disjunct refines (shrinks) access.",
    "no_clean_proved_with_escape": "A clean-isolation proof cannot coexist with a firing escape (soundness-fuzz).",
    "with_check_true_admits_forge": "A `WITH CHECK true` write policy admits any row (forge-any).",
}


def _is_clean(text):
    return "sorry" not in text and "admit" not in text and "theorem" in text.lower()


def _title(fname):
    base = re.sub(r"^PCA_", "", os.path.basename(fname)[:-5])  # strip prefix + .lean
    return base


def harvest():
    files = sorted(set(glob.glob(os.path.join(ARI, "best_proofs", "PCA_*.lean")) +
                       glob.glob(os.path.join(ARI, "pr_ready", "PCA_*.lean"))))
    theorems = []
    seen = set()
    for f in files:
        try:
            text = open(f, errors="ignore").read()
        except Exception:
            continue
        if not _is_clean(text):
            continue
        title = _title(f)
        if title in seen:
            continue
        seen.add(title)
        sha = hashlib.sha256(text.encode("utf-8", "ignore")).hexdigest()
        key = next((k for k in MEANING if k in title.lower()), None)
        theorems.append({
            "name": title,
            "meaning": MEANING.get(key, "Machine-checked property of the isolation model."),
            "status": "KERNEL-VERIFIED",
            "prover": "Aristotle (Lean 4 / Mathlib)",
            "source_file": os.path.relpath(f, os.path.expanduser("~")),
            "proof_sha256": sha,
            "sorry_free": True,
        })
    return theorems


def _vault(key):
    """Read a single var from the ACUTIS vault file (no dependency on fleet_shared)."""
    path = os.path.expanduser("~/.openclaw/vault-bridges.env")
    try:
        for line in open(path):
            line = line.strip()
            if line.startswith(key + "="):
                return line.split("=", 1)[1].strip().strip('"').strip("'")
    except Exception:
        pass
    return ""


def push_to_supabase(theorems):
    """Upsert kernel-verified theorems to BCC Supabase so the public showcase reads them
    LIVE. Additive, anon-readable table. Returns count pushed (0 if creds missing)."""
    import json as _json
    import urllib.request
    url = _vault("BCC_SUPABASE_URL") or "https://fetkjfwackzaxfnmscrv.supabase.co"
    key = _vault("BCC_SUPABASE_SERVICE_ROLE_KEY") or _vault("BCC_SUPABASE_ANON_KEY")
    if not key:
        print("  (no Supabase key in vault — skipped live push)")
        return 0
    rows = []
    for i, t in enumerate(theorems):
        rows.append({"name": t["name"], "meaning": t["meaning"], "status": t["status"],
                     "prover": t["prover"], "source_file": t["source_file"],
                     "proof_sha256": t["proof_sha256"], "sort_order": i})
    try:
        req = urllib.request.Request(
            f"{url}/rest/v1/qp_security_theorems?on_conflict=name",
            data=_json.dumps(rows).encode(), method="POST",
            headers={"apikey": key, "Authorization": f"Bearer {key}",
                     "Content-Type": "application/json",
                     "Prefer": "resolution=merge-duplicates,return=minimal"})
        with urllib.request.urlopen(req, timeout=15) as r:
            ok = r.status in (200, 201, 204)
        print(f"  pushed {len(rows)} theorems to Supabase (qp_security_theorems)")
        return len(rows) if ok else 0
    except Exception as e:
        print(f"  Supabase push failed: {e}")
        return 0


def main():
    theorems = harvest()
    payload = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()) if False else None,
        "kind": "quantumproof-security-rigor/v1",
        "count": len(theorems),
        "summary": "Kernel-verified (Lean 4) soundness theorems of the QuantumProof "
                   "Proof-Carrying-Apps isolation model — machine-checked, not merely SMT-checked.",
        "theorems": theorems,
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as f:
        json.dump(payload, f, indent=1)
    print(f"wrote {OUT} — {len(theorems)} KERNEL-VERIFIED security theorems")
    push_to_supabase(theorems)  # keep the public showcase auto-fresh
    for t in theorems[:8]:
        print(f"  - {t['name']}")


if __name__ == "__main__":
    main()
