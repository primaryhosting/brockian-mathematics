"""engine.verify — the single AXLE verification core.

One home for the proof-verification machinery that had drifted into five copies across
the Aristotle harvest path (`axle_verify.py`, `axle_axiom_audit.py`, `cross_check.py`,
`catalogue_domains.py`, `auto_pr.py`) and a differently-shaped copy in the registry
attest path (`scripts/attest.py`). This module owns:

  * `normalize` / `content_hash` — the ONE canonical proof-content form + its hash. Every
    caller on the harvest hash path imports these so a formatting change lands once.
  * `qualified_decls` — fully-qualified `#print axioms` targets via a namespace/section
    stack (a bare name fails to resolve at end-of-file inside a namespace).
  * `axiom_audit` — submit a proof + `#print axioms` probes to AXLE, parse the axiom set,
    return a strict trusted/None verdict.
  * `compile_check` — the strict compile verdict (delegates to axle_client.check).

`axle_client` stays the transport; this is the shared *semantics* layer above it. Content
normalization and probe-target selection can be supplied by the caller, because the two
paths legitimately differ: the harvest path hoists imports + scrapes decls via
`qualified_decls`; `scripts/attest.py` flattens Brockian dependency bodies and passes an
explicit names list (see step 4 of the unified-proof-engine spec). Pinned to lean-4.32.2.
"""
from __future__ import annotations

import hashlib
import os
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "scripts"))
import axle_client as ax  # noqa: E402

# The trusted kernel axioms. A PROVED proof may depend on these and nothing else.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SAFE = ALLOWED_AXIOMS  # legacy alias used by the harvest callers

# One Lean environment for the whole engine.
DEFAULT_ENV = os.environ.get("AXLE_ENV", "lean-4.32.2")
AUDIT_TAIL = int(os.environ.get("AXLE_AXIOM_TAIL", "3"))

_NS = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*)")
_SEC = re.compile(r"^section\b\s*([A-Za-z_][\w'.]*)?")
_END = re.compile(r"^end\b\s*([A-Za-z_][\w'.]*)?")
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)")


def normalize(content: str) -> str:
    """Hoist deduped imports to the top — the ONE canonical content form. Every harvest
    caller (axle_verify, axle_axiom_audit, cross_check, catalogue_domains, auto_pr) uses
    this so their content hashes line up; the catalogue's promotion gate is a hash match."""
    imports, body = [], []
    for line in content.splitlines():
        if line.strip().startswith("import "):
            if line.strip() not in imports:
                imports.append(line.strip())
        else:
            body.append(line)
    return "\n".join(imports + [""] + body)


def content_hash(content: str) -> str:
    """sha256 of the normalized content, first 16 hex chars. Shared by every leg so the
    same proof produces the same hash across verify / audit / catalogue / auto_pr."""
    return hashlib.sha256(normalize(content).encode()).hexdigest()[:16]


def qualified_decls(text: str) -> list:
    """Fully-qualified names of every theorem/lemma, in source order.

    `#print axioms` runs at end-of-file (outside any namespace the proof opened), so a bare
    declaration name fails to resolve ("unknown constant"). Track the namespace/section
    stack to build the fully-qualified name Lean accepts. `end` (named or not) pops the most
    recent scope; only `namespace` scopes contribute to the name path — `section` do not."""
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


def axioms_in_line(line) -> list | None:
    """Axiom names in ONE `#print axioms` info line, in printed order, or None if the line
    is not an axioms report. "does not depend on any axioms" → []; "depends on axioms:
    [a, b, c]" → [a, b, c]. Used both for the aggregate audit and for attest's per-decl
    attribution (it matches a specific declaration's line, then parses it here)."""
    s = str(line)
    if "does not depend on any axioms" in s:
        return []
    # AXLE/Lean may line-wrap longer dependency lists inside the brackets.  Keep
    # unknown evidence fail-closed, but parse a complete multiline bracketed list.
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", s, re.DOTALL)
    if m:
        return [a.strip() for a in m.group(1).split(",") if a.strip()]
    return None


def parse_axioms(infos) -> set:
    """Union the axiom sets reported by every `#print axioms` info line. A hole yields
    `sorryAx` in the list."""
    used = set()
    for line in infos or []:
        got = axioms_in_line(line)
        if got:
            used |= set(got)
    return used


def axiom_audit(content: str, *, probe_targets=None, preamble: str = "",
                env: str | None = None, tail: int | None = None,
                timeout: int = 120) -> dict:
    """Cloud axiom audit: submit `content` plus `#print axioms <t>` for each probe target
    to AXLE, read the axiom set back from lean_messages.infos, and return a strict verdict.

    Returns {trusted: bool|None, axioms, extra_axioms, environment, detail}.
      trusted is True iff the content compiles cleanly AND every probed declaration depends
      only on ALLOWED_AXIOMS with no sorryAx and no sorry/admit warning; False if it
      compiles but is unsound; None if it does not compile / errors / has no target.

    probe_targets: names to `#print axioms`. Defaults to qualified_decls(normalize(content))
      tail. Callers with their own decl model (attest.py) pass an explicit list.
    preamble: text inserted before the probes (e.g. `open Some.Namespace`) for callers
      whose targets are not fully qualified.
    """
    env = env or DEFAULT_ENV
    tail = AUDIT_TAIL if tail is None else tail
    text = normalize(content)
    if probe_targets is None:
        probe_targets = qualified_decls(text)[-tail:] if tail else qualified_decls(text)
    if not probe_targets:
        return {"trusted": None, "axioms": [], "extra_axioms": [],
                "environment": env, "detail": "no theorem/lemma found"}
    probes = "\n".join(f"#print axioms {t}" for t in probe_targets)
    probe = text + "\n\n" + (preamble + "\n" if preamble else "") + probes
    try:
        resp = ax._post("check", {"content": probe, "environment": env}, timeout=timeout)
    except Exception as e:  # noqa: BLE001 — network/service error recorded as unknown
        return {"trusted": None, "axioms": [], "extra_axioms": [],
                "environment": env, "detail": f"axle error: {str(e)[:160]}"}
    lm = resp.get("lean_messages") or {}
    errors = list(lm.get("errors") or [])
    warnings = list(lm.get("warnings") or [])
    if not resp.get("okay", False) or errors:
        return {"trusted": None, "axioms": [], "extra_axioms": [], "environment": env,
                "detail": "compile error: " + (str(errors[:1]) or "not okay")[:180]}
    axioms = parse_axioms(lm.get("infos"))
    sorry_warned = any("sorry" in str(w).lower() or "admit" in str(w).lower()
                       for w in warnings)
    extra = sorted(a for a in axioms if a not in ALLOWED_AXIOMS)
    trusted = (not sorry_warned) and ("sorryAx" not in axioms) and not extra
    return {"trusted": trusted, "axioms": sorted(axioms), "extra_axioms": extra,
            "environment": env, "detail": None}


def compile_check(content: str, *, env: str | None = None, timeout: int = 120):
    """Strict compile verdict via axle_client.check (compiles ∧ no errors ∧ no sorry).
    Returns the axle_client.AxleResult. Content is normalized first."""
    return ax.check(normalize(content), env=env or DEFAULT_ENV, timeout=timeout)
