"""Overclaim firewall + registry self-consistency audit (roadmap #35 + #36).

Two machine-checked invariants over registry/theorems.json, complementing Codex's
docs/PROOF-DEPENDENCY-MAP.md and scripts/audit_registry_opens.py:

  #35 OVERCLAIM FIREWALL — a declaration registered PROVED must independently earn it:
      axioms ⊆ {propext, Classical.choice, Quot.sound} AND no native_decide AND AXLE verdict
      == verified. Because a PROVED theorem is independently axiom-checked, it *cannot*
      transitively rest on an open CONDITIONAL/CONJECTURE without failing this check — so the
      firewall is exactly this local invariant, enforced globally.

  #36 SELF-CONSISTENCY — the register vocabulary is used honestly:
      - every CONDITIONAL carries a conditional_rung ∈ {classical, literature, open};
      - every CONJECTURE is a Prop container (kind def/abbrev/conjecture), never a theorem/lemma;
      - no stale-open: a `*Target`/`*Conjecture`-style Prop container must not ALSO have a
        sibling theorem that already discharges it (that pattern means it should be reclassified).

Exit non-zero on any violation so this can gate CI. Read-only; prints a clean bill or the
exact violations.
"""
from __future__ import annotations

import json
import os
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VALID_RUNGS = {"classical", "literature", "open"}
REGISTRY = "registry/theorems.json"


def load() -> list[dict]:
    if not os.path.exists(REGISTRY):
        print(f"FATAL: {REGISTRY} not found", file=sys.stderr)
        sys.exit(2)
    return json.load(open(REGISTRY)).get("theorems", [])


def check_firewall(thms: list[dict]) -> list[str]:
    """#35 — every PROVED decl independently earns it."""
    v = []
    for t in thms:
        if t.get("register") != "PROVED":
            continue
        name = t["name"]
        ax = set(t.get("axioms") or [])
        if not ax.issubset(ALLOWED_AXIOMS):
            v.append(f"[firewall] PROVED {name}: axioms escape standard set: {sorted(ax - ALLOWED_AXIOMS)}")
        if t.get("flags", {}).get("native_decide"):
            v.append(f"[firewall] PROVED {name}: uses native_decide (compiler-trusted) — must be COMPUTATION")
        if t["verification"]["axle"]["verdict"] != "verified":
            v.append(f"[firewall] PROVED {name}: AXLE verdict is {t['verification']['axle']['verdict']!r}, not verified")
        if not t["verification"].get("axioms_ok", False):
            v.append(f"[firewall] PROVED {name}: axioms_ok is false")
    return v


def check_self_consistency(thms: list[dict]) -> list[str]:
    """#36 — honest use of the register vocabulary."""
    v = []
    # discharged_by must resolve UNAMBIGUOUSLY: a fully-qualified PROVED name, or a
    # short name matching exactly one PROVED entry (mirrors scripts/gen_registry.py).
    proved_full = {t["name"] for t in thms if t.get("register") == "PROVED"}
    proved_by_short: dict[str, set[str]] = {}
    for n in proved_full:
        proved_by_short.setdefault(n.split(".")[-1], set()).add(n)
    for t in thms:
        reg, name, kind = t.get("register"), t["name"], t.get("kind")
        if reg == "CONDITIONAL":
            rung = t.get("conditional_rung")
            if rung not in VALID_RUNGS:
                v.append(f"[consistency] CONDITIONAL {name}: rung {rung!r} not in {sorted(VALID_RUNGS)}")
        if reg == "DISCHARGED":
            db = t.get("discharged_by")
            if not db:
                v.append(f"[consistency] DISCHARGED {name}: no discharged_by recorded")
            elif db in proved_full or len(proved_by_short.get(db, ())) == 1:
                pass  # unambiguous resolution — honest discharge
            elif len(proved_by_short.get(db, ())) > 1:
                v.append(
                    f"[consistency] DISCHARGED {name}: discharged_by {db!r} is AMBIGUOUS among "
                    f"PROVED theorems {sorted(proved_by_short[db])} — must use the full name"
                )
            else:
                v.append(f"[consistency] DISCHARGED {name}: discharged_by {db!r} is not a PROVED theorem in-core")
        if reg == "CONJECTURE" and kind in ("theorem", "lemma"):
            v.append(f"[consistency] CONJECTURE {name}: kind is {kind!r} — a conjecture must be a Prop container, not a theorem")
    # stale-open: a Prop-container target that already has a proving sibling in the same module
    by_mod: dict[str, list[dict]] = {}
    for t in thms:
        by_mod.setdefault(t["module"], []).append(t)
    for mod, ts in by_mod.items():
        names = {t["name"].split(".")[-1] for t in ts}
        for t in ts:
            short = t["name"].split(".")[-1]
            if t.get("register") in ("CONJECTURE",) and (
                short.endswith("Target") or short.endswith("Conjecture")
            ):
                base = short.removesuffix("Target").removesuffix("Conjecture")
                # a proved sibling literally named after the base is a stale-open smell
                if any(n != short and base and n.startswith(base) and
                       any(x["name"].split(".")[-1] == n and x.get("register") == "PROVED" for x in ts)
                       for n in names):
                    v.append(f"[consistency] stale-open: CONJECTURE {short} in {mod} has a PROVED sibling matching {base!r} — reclassify")
    return v


def main() -> int:
    thms = load()
    fw = check_firewall(thms)
    sc = check_self_consistency(thms)
    n_proved = sum(1 for t in thms if t.get("register") == "PROVED")
    n_cond = sum(1 for t in thms if t.get("register") == "CONDITIONAL")
    n_disc = sum(1 for t in thms if t.get("register") == "DISCHARGED")
    n_conj = sum(1 for t in thms if t.get("register") == "CONJECTURE")
    print(f"registry: {len(thms)} entries | PROVED {n_proved} | CONDITIONAL {n_cond} | DISCHARGED {n_disc} | CONJECTURE {n_conj}")
    if not fw:
        print(f"#35 overclaim-firewall: CLEAN — all {n_proved} PROVED are axiom-clean, no native_decide, AXLE-verified")
    else:
        print(f"#35 overclaim-firewall: {len(fw)} VIOLATION(S)")
        for x in fw:
            print("  " + x)
    if not sc:
        print(f"#36 self-consistency: CLEAN — every CONDITIONAL has a rung, every CONJECTURE is a container, no stale-opens")
    else:
        print(f"#36 self-consistency: {len(sc)} VIOLATION(S)")
        for x in sc:
            print("  " + x)
    return 0 if not (fw or sc) else 1


if __name__ == "__main__":
    raise SystemExit(main())
