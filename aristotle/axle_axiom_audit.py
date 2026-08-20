#!/usr/bin/env python3
"""axle_axiom_audit.py — independent AXIOM audit in the cloud (AXLE).

A proof can COMPILE yet smuggle in an extra axiom or a `sorryAx` (a hole that Lean
accepts with only a warning). cross_check.py does this audit LOCALLY via
`lake env lean` + `#print axioms`, but local Lean cannot run on this RAM-starved box
— a single Mathlib load thrashes swap indefinitely — so the local audit never
produces a verdict and cloud-verified proofs stall forever at PROVED_UNVERIFIED.

This runs the SAME soundness audit CLOUD-side via AXLE: it resubmits each
AXLE-verified proof with `#print axioms <decls>` appended and reads the actual axiom
set back from `lean_messages.infos`. A proof is `trusted` iff it compiles cleanly
AND every audited declaration depends only on the trusted kernel axioms
{propext, Classical.choice, Quot.sound}, with no `sorryAx` anywhere.

This is the audit that promotes a proof to registry PROVED (see catalogue_domains
`independent_ok`). It only audits proofs AXLE already verified — those are
self-contained (Mathlib-only), so the resubmission compiles cloud-side; proofs that
import Brockian-local modules never reach `verified=True` and are skipped here.

Keyed/normalized IDENTICALLY to axle_verify.py and cross_check.py so the shared
content hash lines up across all three legs (catalogue requires a hash match).
Resumable via axle_axiom_audit.json, capped (AXLE_AXIOM_MAX) + paced (AXLE_PACE).
Cloud round-trip is ~1-3s/proof — no local Mathlib tax.
"""
import glob
import hashlib
import json
import os
import pathlib
import re
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import axle_client as ax  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "best_proofs"
STATE = ROOT / "axle_axiom_audit.json"
AXLE_STATE = ROOT / "axle_verify.json"
SAFE = {"propext", "Classical.choice", "Quot.sound"}
_NS = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*)")
_SEC = re.compile(r"^section\b\s*([A-Za-z_][\w'.]*)?")
_END = re.compile(r"^end\b\s*([A-Za-z_][\w'.]*)?")
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)")
MAX = int(os.environ.get("AXLE_AXIOM_MAX", "40"))
PACE = float(os.environ.get("AXLE_PACE", "1.0"))
# how many trailing declarations to audit (the main theorem is last; auditing the
# tail also covers a proof whose final decl is a corollary of earlier lemmas).
AUDIT_TAIL = int(os.environ.get("AXLE_AXIOM_TAIL", "3"))


def normalize(content: str) -> str:
    """Hoist deduped imports to the top — identical to axle_verify.normalize and
    cross_check.normalize so the content hash matches across all three legs."""
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


def _atomic_write(path: pathlib.Path, obj) -> None:
    """Write JSON via a temp file + rename so a concurrent reader (catalogue_domains
    consumes this state in the live conveyor) never sees a half-written file."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=1))
    os.replace(tmp, path)


def qualified_decls(text: str) -> list:
    """Fully-qualified names of every theorem/lemma, in source order.

    `#print axioms` runs at end-of-file (outside any namespace the proof opened), so a
    bare declaration name fails to resolve ("unknown constant"). We track the
    namespace/section stack to build the fully-qualified name Lean will accept. `end`
    (with or without a name) pops the most recent scope; only `namespace` scopes
    contribute to the name path — `section` scopes do not."""
    stack = []  # list of (kind, name)
    out = []
    for line in text.splitlines():
        st = line.strip()
        m = _NS.match(st)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        if _SEC.match(st):
            stack.append(("sec", _SEC.match(st).group(1) or ""))
            continue
        if _END.match(st):
            if stack:
                stack.pop()
            continue
        d = _DECL.match(st)
        if d:
            ns_path = [n for k, n in stack if k == "ns"]
            out.append(".".join(ns_path + [d.group(1)]))
    return out


def parse_axioms(infos) -> set:
    """Union the axiom sets reported by every `#print axioms` info line.

    Lean prints either "'name' does not depend on any axioms" (→ empty set) or
    "'name' depends on axioms: [a, b, c]". A hole yields `sorryAx` in that list."""
    used = set()
    for line in infos or []:
        s = str(line)
        if "does not depend on any axioms" in s:
            continue
        m = re.search(r"depends on axioms:\s*\[(.*?)\]", s)
        if m:
            used |= {a.strip() for a in m.group(1).split(",") if a.strip()}
    return used


def audit_one(content: str):
    """Return (trusted: bool|None, axioms: sorted list, detail: str|None)."""
    text = normalize(content)
    names = qualified_decls(text)
    if not names:
        return None, [], "no theorem/lemma found"
    probe = text + "\n\n" + "\n".join(f"#print axioms {n}" for n in names[-AUDIT_TAIL:])
    try:
        resp = ax._post("check", {"content": probe, "environment": ax.DEFAULT_ENV},
                        timeout=int(os.environ.get("AXLE_AXIOM_TIMEOUT", "120")))
    except Exception as e:  # noqa: BLE001 — network/service; recorded as unknown
        return None, [], f"axle error: {str(e)[:160]}"
    lm = resp.get("lean_messages") or {}
    errors = list(lm.get("errors") or [])
    warnings = list(lm.get("warnings") or [])
    if not resp.get("okay", False) or errors:
        return None, [], "compile error: " + (str(errors[:1]) or "not okay")[:180]
    axioms = parse_axioms(lm.get("infos"))
    sorry_warned = any("sorry" in str(w).lower() or "admit" in str(w).lower()
                       for w in warnings)
    extra = sorted(a for a in axioms if a not in SAFE)
    trusted = (not sorry_warned) and ("sorryAx" not in axioms) and not extra
    return trusted, sorted(axioms), None


def main():
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    axle = json.loads(AXLE_STATE.read_text()) if AXLE_STATE.exists() else {}
    files = sorted(glob.glob(str(SRC / "*.lean")))

    def eligible(f):
        """Audit only AXLE-verified proofs; (re)audit when new or content changed."""
        b = pathlib.Path(f).name
        av = axle.get(b, {})
        if av.get("verified") is not True:
            return False
        digest = content_hash(open(f, errors="ignore").read())
        prev = state.get(b, {})
        return (prev.get("hash") != digest
                or prev.get("environment") != ax.DEFAULT_ENV
                or prev.get("trusted") is None)  # retry transient nulls

    todo = [f for f in files if eligible(f)][:MAX]
    print(f"{len(files)} best proofs; cloud axiom-auditing {len(todo)} "
          f"(AXLE {ax.DEFAULT_ENV})")
    for f in todo:
        b = pathlib.Path(f).name
        raw = open(f, errors="ignore").read()
        digest = content_hash(raw)
        trusted, axioms, detail = audit_one(raw)
        rec = {"trusted": trusted, "axioms": axioms,
               "extra_axioms": sorted(a for a in axioms if a not in SAFE),
               "environment": ax.DEFAULT_ENV, "hash": digest}
        if detail:
            rec["detail"] = detail
        state[b] = rec
        _atomic_write(STATE, state)
        mark = "OK " if trusted else (".. " if trusted is None else "xx ")
        print(f"  {mark}{b}  {rec.get('extra_axioms') or detail or 'kernel-clean'}")
        time.sleep(PACE)

    trusted = sum(1 for s in state.values() if s.get("trusted") is True)
    flagged = [b for b, s in state.items() if s.get("trusted") is False]
    print(f"\ncloud axiom-audited {len(state)} | kernel-trusted {trusted} | "
          f"FLAGGED {len(flagged)}: {flagged[:6]}")


if __name__ == "__main__":
    main()
