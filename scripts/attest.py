"""Produce an AXLE verification attestation for a Brockian module.

Reads a .lean module, appends `#print axioms` probes for the named declarations, runs
AXLE `check` at the given environment, and writes registry/attestations/<Module>.json
recording the independent verdict + axiom set per declaration (spec §2A / §5).

Usage:
    python3 scripts/attest.py Brockian/GoldbachComb.lean Brockian.GoldbachComb \
        gCount_eq gCount_centered local_covariance [--env lean-4.32.2]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import axle_client  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from engine.verify import ALLOWED_AXIOMS as ALLOWED  # noqa: E402 — single-sourced axioms
from engine.verify import DEFAULT_ENV, axioms_in_line, qualified_decls  # noqa: E402


def _attestation_stem(lean_path: str) -> str:
    """Use the source module stem, not the namespace tail, as the canonical key."""
    return os.path.splitext(os.path.basename(lean_path))[0]


def _kind_of(src: str, name: str) -> str:
    """Detect a declaration's kind from the source (theorem/lemma vs def/abbrev)."""
    # A word boundary is insufficient here: `Factorization` has a word boundary
    # before the dot in `Factorization.isCompactOperator`. Require the complete
    # declaration identifier so a nested theorem cannot shadow its parent structure.
    ident = re.escape(name) + r"(?![\w.'])"
    if re.search(rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:theorem|lemma)\s+{ident}",
                 src, re.MULTILINE):
        return "theorem"
    # The declared name may carry an explicit namespace prefix (`def Factorization.ofCompact`),
    # so allow an optional dotted prefix before the bare identifier — otherwise a prefixed
    # def falls through to the "theorem" default and gets probed with `#print axioms`, which
    # fails to resolve (it is not a proof term and not in the theorem/lemma name set).
    pfx = r"(?:[A-Za-z_][\w'.]*\.)?"
    m = re.search(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev)\s+{pfx}{ident}(.*?):=",
        src, re.MULTILINE | re.DOTALL)
    if m:
        sig = m.group(1)
        # A conjecture container is a NULLARY Prop claim (`def C : Prop := …`), standing in
        # for an open statement. A parameterized Prop-def is a predicate → a definition.
        if re.search(r":\s*Prop\b", sig) and sig.split(":")[0].strip() == "":
            return "conjecture"
        return "def"
    # structures/classes/inductives are definitions, not theorems
    if re.search(rf"^\s*(?:@\[[^\]]*\]\s*)*(?:structure|class|inductive)\s+{pfx}{ident}",
                 src, re.MULTILINE):
        return "def"
    return "theorem"


def _flatten(lean_path: str, _seen: set[str] | None = None) -> str:
    """Produce a self-contained source by inlining `import Brockian.*` dependencies, so a
    module that builds on sibling Brockian modules can be AXLE-checked as one unit (AXLE
    `check` is single-file, Mathlib-only, and cannot resolve local imports). Emits one
    `import Mathlib`, then dependency bodies in topological order, then the target body."""
    _seen = _seen if _seen is not None else set()
    src = open(lean_path, encoding="utf-8").read()
    dep_bodies: list[str] = []
    body_lines: list[str] = []
    for line in src.splitlines():
        s = line.strip()
        if s.startswith("import Brockian."):
            mod = s.split()[1]  # e.g. Brockian.Core
            if mod in _seen:
                continue
            _seen.add(mod)
            dep_path = os.path.join("Brockian", mod.split(".", 1)[1].replace(".", "/") + ".lean")
            if os.path.exists(dep_path):
                # inline the dependency (recursively), stripping its own import Mathlib
                dep = _flatten(dep_path, _seen)
                dep = "\n".join(l for l in dep.splitlines()
                                if l.strip() != "import Mathlib")
                dep_bodies.append(dep)
            continue
        if s == "import Mathlib":
            continue
        body_lines.append(line)
    return "import Mathlib\n" + "\n".join(dep_bodies) + "\n" + "\n".join(body_lines)


def attest(lean_path: str, namespace: str, names: list[str], env: str) -> dict:
    src = open(lean_path, encoding="utf-8").read()
    flat = _flatten(lean_path)  # AXLE-checkable unit (inlines Brockian deps)
    kinds = {n: _kind_of(src, n) for n in names}
    # `#print axioms` only makes sense for proof terms; on a `structure`/`class` it errors
    # and would fail the whole check. Probe axioms only for theorem/lemma declarations.
    probe_names = [n for n in names if kinds[n] == "theorem"]
    # Resolve each short name to its FULLY-QUALIFIED name. Declarations may live in nested
    # namespaces (e.g. Brockian.Weyl.Operator.IsSymmetric.foo), and the `namespace` arg is
    # not always the real top namespace. `open {namespace} in #print axioms {short}` then
    # fails to resolve under lean-4.32.2 (4.32.0 was looser). Fully-qualified `#print
    # axioms {fqn}` resolves regardless of nesting — same approach as axle_axiom_audit.
    fqn_by_short: dict[str, str] = {}
    for fq in qualified_decls(flat):
        fqn_by_short.setdefault(fq.split(".")[-1], fq)

    def fqn(n: str) -> str:
        return fqn_by_short.get(n, f"{namespace}.{n}")

    probe = flat + "\n\n" + "\n".join(
        f"#print axioms {fqn(n)}" for n in probe_names) + "\n"
    # The probe recompiles the WHOLE module + #print axioms; large modules (heavy ℂ
    # character sums, big case analyses) need more than the old hard 300s. Configurable
    # via ATTEST_TIMEOUT so a big assembled module doesn't false-fail on timeout.
    _timeout = int(os.environ.get("ATTEST_TIMEOUT", "600"))
    r = axle_client.check(probe, env=env, timeout=_timeout)
    infos = (r.raw.get("lean_messages") or {}).get("infos", [])

    def axioms_for(n: str) -> list[str] | None:
        needle = f"{fqn(n)}'"  # Lean prints 'fully.qualified.name' in the axioms line
        for i in infos:
            s = i if isinstance(i, str) else str(i)
            if needle in s and "axioms" in s:
                got = axioms_in_line(s)  # shared parser (engine.verify)
                return got if got is not None else []
        return None

    decls = []
    for n in names:
        kind = kinds[n]
        if kind == "theorem":
            ax = axioms_for(n)
            ax_ok = (ax is not None and set(ax).issubset(ALLOWED))
        else:
            # defs/structures/conjecture-containers carry no proof-axiom footprint;
            # their register (DEFINITION/CONJECTURE) does not depend on axioms.
            ax, ax_ok = None, True
        decls.append({
            "name": f"{namespace}.{n}",
            "kind": kind,
            "axle_verdict": "verified" if r.verified else "failed",
            "axioms": ax,
            "axioms_ok": ax_ok,
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
    ap.add_argument("--env", default=DEFAULT_ENV)  # lean-4.32.2 (4.32.0 deprecated)
    args = ap.parse_args()
    att = attest(args.lean_path, args.namespace, args.names, args.env)
    out = os.path.join("registry", "attestations", _attestation_stem(args.lean_path) + ".json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    json.dump(att, open(out, "w"), indent=2)
    print(json.dumps(att, indent=2))
    return 0 if att["module_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
