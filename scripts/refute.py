"""refute.py — the finite counterexample factory (the FALSE half of the certificate factory).

Certificates are the unit of progress: TRUE needs a proof artifact, FALSE needs an explicit model.
This is the FALSE side — a settle-machine for equational-law implications (the magma / ETP /
SAIR-distillation-Stage-2 shape). Given laws A, B over one binary op, it searches finite magmas
for a COUNTERMODEL — a magma satisfying A but not B — which refutes "A entails B". It then EMITS a
self-contained Lean refutation target proving, by kernel `decide` on the explicit table:

    countermodel : (∀ vars, A[op]) ∧ ¬ (∀ vars, B[op])
    not_entails  : ¬ ∀ (m : Fin n → Fin n → Fin n), (∀ vars, A[m]) → (∀ vars, B[m])

`scripts/settle.py --refute <emitted>` then independently AXLE-verifies it → a REFUTED certificate.
Search is exhaustive for n ≤ 3 and honestly-capped random sampling for larger n (logged, never
claimed exhaustive). No countermodel found within budget ⇒ INCONCLUSIVE, never "true".

Law grammar:  T := 'x'|'y'|'z' | T '*' T | '(' T ')'   (left-assoc);   law := T '=' T
Example:      refute.py --A "x*x = x" --B "x*y = y*x"      (idempotent ⊬ commutative)
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import re


# ── tiny term language ────────────────────────────────────────────────────────
def tokenize(s: str) -> list[str]:
    return re.findall(r"[xyz]|\*|\(|\)", s)


def parse(s: str):
    """Return an AST: ('var', name) | ('op', left, right). Left-assoc '*'."""
    toks = tokenize(s)
    pos = 0

    def atom():
        nonlocal pos
        t = toks[pos]
        if t == "(":
            pos += 1
            e = expr()
            assert toks[pos] == ")", f"expected ) in {s!r}"
            pos += 1
            return e
        assert t in ("x", "y", "z"), f"unexpected token {t!r} in {s!r}"
        pos += 1
        return ("var", t)

    def expr():
        nonlocal pos
        node = atom()
        while pos < len(toks) and toks[pos] == "*":
            pos += 1
            node = ("op", node, atom())
        return node

    e = expr()
    assert pos == len(toks), f"trailing tokens in {s!r}"
    return e


def law_vars(*asts) -> list[str]:
    seen: set[str] = set()
    def walk(a):
        if a[0] == "var":
            seen.add(a[1])
        else:
            walk(a[1]); walk(a[2])
    for a in asts:
        walk(a)
    return [v for v in ("x", "y", "z") if v in seen]


def ev(ast, env: dict, table) -> int:
    if ast[0] == "var":
        return env[ast[1]]
    return table[ev(ast[1], env, table)][ev(ast[2], env, table)]


def holds(lhs, rhs, n: int, table, vs: list[str]) -> bool:
    for vals in itertools.product(range(n), repeat=len(vs)):
        env = dict(zip(vs, vals))
        if ev(lhs, env, table) != ev(rhs, env, table):
            return False
    return True


# ── search ────────────────────────────────────────────────────────────────────
def all_tables(n: int):
    """Every binary op on Fin n as a nested list; exhaustive."""
    cells = n * n
    for flat in itertools.product(range(n), repeat=cells):
        yield [list(flat[i * n:(i + 1) * n]) for i in range(n)]


def search(A, B, max_n: int, cap: int):
    (la, ra), (lb, rb) = A, B
    vs = law_vars(la, ra, lb, rb) or ["x"]
    log = []
    import random  # local; seeded deterministically for reproducibility
    rng = random.Random(1729)
    for n in range(1, max_n + 1):
        space = n ** (n * n)
        exhaustive = space <= cap
        tried = 0
        gen = all_tables(n) if exhaustive else iter(
            [[[rng.randrange(n) for _ in range(n)] for _ in range(n)] for _ in range(cap)]
        )
        for table in gen:
            tried += 1
            if holds(la, ra, n, table, vs) and not holds(lb, rb, n, table, vs):
                log.append(f"n={n}: countermodel after {tried} ({'exhaustive' if exhaustive else 'sampled'})")
                return n, table, vs, log
        log.append(f"n={n}: none in {tried} ({'exhaustive' if exhaustive else f'sampled cap={cap}'})")
    return None, None, vs, log


# ── Lean emission ──────────────────────────────────────────────────────────────
def term_to_lean(ast) -> str:
    if ast[0] == "var":
        return ast[1]
    return f"op ({term_to_lean(ast[1])}) ({term_to_lean(ast[2])})"


def emit_lean(n, table, A, B, vs, ns, a_str, b_str) -> str:
    rows = ",".join("![" + ",".join(f"({c} : Fin {n})" for c in row) + "]" for row in table)
    binder = " ".join(vs)
    (la, ra), (lb, rb) = A, B
    aeq = f"{term_to_lean(la)} = {term_to_lean(ra)}"
    beq = f"{term_to_lean(lb)} = {term_to_lean(rb)}"
    forall_a = f"∀ {binder} : Fin {n}, {aeq}"
    forall_b = f"∀ {binder} : Fin {n}, {beq}"
    # generic law bodies over an arbitrary op m, for the not_entails statement
    def body(ast, m):
        if ast[0] == "var":
            return ast[1]
        return f"{m} ({body(ast[1], m)}) ({body(ast[2], m)})"
    gen_a = f"∀ {binder} : Fin {n}, {body(la,'m')} = {body(ra,'m')}"
    gen_b = f"∀ {binder} : Fin {n}, {body(lb,'m')} = {body(rb,'m')}"
    return f'''/-
  Refutation certificate (finite countermodel) — generated by scripts/refute.py
  Claim refuted:  ({a_str})  ⊬  ({b_str})
  A magma of order {n} satisfies A but not B, so A does not entail B.
  Proof is by kernel `decide` on the explicit multiplication table (COMPUTATION).
-/
import Mathlib

namespace {ns}

/-- The countermodel: an order-{n} magma satisfying `{a_str}` but not `{b_str}`. -/
def op : Fin {n} → Fin {n} → Fin {n} := ![{rows}]

/-- Kernel-checked: the table satisfies A and violates B. -/
theorem countermodel : ({forall_a}) ∧ ¬ ({forall_b}) := by decide

/-- Hence A does not entail B over magmas of order {n}. -/
theorem not_entails :
    ¬ ∀ (m : Fin {n} → Fin {n} → Fin {n}), ({gen_a}) → ({gen_b}) :=
  fun h => countermodel.2 (h op countermodel.1)

end {ns}
'''


def main() -> int:
    ap = argparse.ArgumentParser(description="Finite counterexample factory for equational-law implications.")
    ap.add_argument("--A", required=True, help='hypothesis law, e.g. "x*x = x"')
    ap.add_argument("--B", required=True, help='conclusion law to refute, e.g. "x*y = y*x"')
    ap.add_argument("--max-n", type=int, default=3)
    ap.add_argument("--cap", type=int, default=200000, help="exhaustive if n^(n*n) <= cap, else sample cap tables")
    ap.add_argument("--slug", default=None, help="output slug (default derived)")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    def eq(s):
        l, r = s.split("=")
        return (parse(l), parse(r))

    A, B = eq(a.A), eq(a.B)
    n, table, vs, log = search(A, B, a.max_n, a.cap)

    if n is None:
        result = {"verdict": "INCONCLUSIVE", "A": a.A, "B": a.B, "max_n": a.max_n, "search": log,
                  "note": "no countermodel within budget — NOT a proof that A entails B"}
        print(json.dumps(result, indent=2) if a.json else
              f"? refute: INCONCLUSIVE — no order≤{a.max_n} countermodel to ({a.A}) ⊬ ({a.B}) within budget")
        return 2

    slug = a.slug or ("refute-" + re.sub(r"[^a-z0-9]+", "-", (a.A + "-not-" + a.B).lower()).strip("-")[:48])
    ns = "Brockian.Refute." + re.sub(r"[^A-Za-z0-9]", "", slug.title())
    outdir = f"aristotle/{slug}"
    os.makedirs(outdir, exist_ok=True)
    lean = emit_lean(n, table, A, B, vs, ns, a.A, a.B)
    path = f"{outdir}/target.lean"
    open(path, "w").write(lean)

    result = {"verdict": "COUNTERMODEL", "A": a.A, "B": a.B, "order": n, "table": table,
              "namespace": ns, "target": path, "search": log,
              "next": f"python3 scripts/settle.py {path} --refute {path}"}
    if a.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"⊘ refute: COUNTERMODEL of order {n} — ({a.A}) ⊬ ({a.B})")
        for row in table:
            print("    " + " ".join(str(c) for c in row))
        print(f"  emitted → {path}")
        print(f"  verify  → python3 scripts/settle.py {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
