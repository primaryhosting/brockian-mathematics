#!/usr/bin/env python3
"""pipeline_attest_bridge.py — print exact formalize→verify commands (no network).

Given a Brockian .lean path (and optional declaration short-names), emit the
shell lines an operator (or agent) should run to:

  1. no-theater lint
  2. AXLE attest (scripts/attest.py)  — *print only*; does not call AXLE
  3. registry join (scripts/gen_registry.py)
  4. optional settle certificate factory (scripts/settle.py)
  5. optional pipeline ledger attempt (pipeline_cli)

Designed so concurrent agents can wire formalize→verify without clobbering
attestations: this script never writes registry/* or hits the network.

Usage (from repo root):
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean thm1 thm2
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --namespace Brockian.Foo
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --pipeline-id math-rh-schema
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --refute aristotle/foo-neg/target.lean
  python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Any

# Keep extraction independent of settle/attest imports so this never touches AXLE.
sys.path.insert(0, os.path.dirname(__file__))
import no_theater_lint  # _blank_block_comments only

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s(){}:]+)",
    re.M,
)
NS_RE = re.compile(r"^namespace\s+([A-Za-z0-9_.']+)", re.M)
DEFAULT_ENV = "lean-4.32.0"


def discover_names(path: str) -> list[str]:
    src = open(path, encoding="utf-8").read()
    src = no_theater_lint._blank_block_comments(src)
    src = "\n".join(re.sub(r"--.*$", "", ln) for ln in src.splitlines())
    return sorted(set(DECL_RE.findall(src)))


def discover_namespace(path: str) -> str | None:
    m = NS_RE.search(open(path, encoding="utf-8").read())
    return m.group(1) if m else None


def stem_of(path: str) -> str:
    base = os.path.basename(path)
    return base[:-5] if base.endswith(".lean") else base


def infer_namespace(path: str, explicit: str | None) -> str:
    if explicit:
        return explicit
    found = discover_namespace(path)
    if found:
        return found
    # Brockian/Foo.lean → Brockian.Foo (common convention)
    p = path.replace("\\", "/")
    if p.startswith("Brockian/") and p.endswith(".lean"):
        return "Brockian." + stem_of(path)
    raise SystemExit(
        f"could not infer namespace for {path}; pass --namespace Brockian.<Module>"
    )


def build_plan(
    lean_path: str,
    names: list[str],
    namespace: str,
    env: str,
    refute: str | None,
    pipeline_id: str | None,
    include_settle: bool,
) -> dict[str, Any]:
    if not names:
        names = discover_names(lean_path)
    if not names:
        raise SystemExit(f"no declarations found in {lean_path}; pass names explicitly")

    stem = stem_of(lean_path)
    # Short names only for attest.py (not fully-qualified)
    short = [n.split(".")[-1] for n in names]
    attest_cmd = (
        f"python3 scripts/attest.py {lean_path} {namespace} "
        + " ".join(short)
        + f" --env {env}"
    )
    lint_cmd = f"python3 scripts/no_theater_lint.py {lean_path}"
    registry_cmd = "python3 scripts/gen_registry.py"
    settle_cmd = f"python3 scripts/settle.py {lean_path} --env {env}"
    if refute:
        settle_cmd += f" --refute {refute}"

    commands: list[dict[str, str]] = [
        {
            "step": "lint",
            "why": "no-theater gate before any AXLE spend",
            "cmd": lint_cmd,
        },
        {
            "step": "attest",
            "why": f"writes registry/attestations/{stem}.json via AXLE@{env}",
            "cmd": attest_cmd,
        },
        {
            "step": "registry",
            "why": "derive registers → registry/theorems.json + REGISTRY.md "
            "(only root-imported modules count)",
            "cmd": registry_cmd,
        },
    ]
    if include_settle:
        commands.append(
            {
                "step": "settle",
                "why": "certificate factory → registry/certificates/<Module>.json "
                "(gitignored attempt ledger; dual-race if --refute)",
                "cmd": settle_cmd,
            }
        )

    pipeline_cmds: list[dict[str, str]] = []
    if pipeline_id:
        # Operator still sets --result / --axle-verified from certificate verdict.
        pipeline_cmds.append(
            {
                "step": "pipeline_attempt_proved",
                "why": "after VERIFIED certificate + axioms_clean",
                "cmd": (
                    f"python3 -m pipeline.scripts.pipeline_cli attempt {pipeline_id} "
                    f"--mode formalize --result proved --axioms-clean --axle-verified "
                    f"--artifact {lean_path} "
                    f"--artifact registry/attestations/{stem}.json "
                    f"--artifact registry/certificates/{stem}.json "
                    f'--note "settled via bridge plan"'
                ),
            }
        )
        pipeline_cmds.append(
            {
                "step": "pipeline_attempt_refuted",
                "why": "after settle verdict=REFUTED (negation verified)",
                "cmd": (
                    f"python3 -m pipeline.scripts.pipeline_cli attempt {pipeline_id} "
                    f"--mode refute --result refuted "
                    f"--artifact {lean_path} "
                    + (f"--artifact {refute} " if refute else "")
                    + f'--note "refutation certificate"'
                ),
            }
        )
        pipeline_cmds.append(
            {
                "step": "pipeline_ledger",
                "why": "rebuild pipeline/ledger/LEDGER.md + problems.json",
                "cmd": "python3 -m pipeline.scripts.pipeline_cli ledger",
            }
        )

    return {
        "lean_path": lean_path,
        "namespace": namespace,
        "stem": stem,
        "env": env,
        "names": short,
        "n_names": len(short),
        "refute": refute,
        "pipeline_id": pipeline_id,
        "attestation_out": f"registry/attestations/{stem}.json",
        "certificate_out": f"registry/certificates/{stem}.json",
        "import_hint": f"import Brockian.{stem}   # must appear in Brockian.lean for gen_registry",
        "commands": commands,
        "pipeline_commands": pipeline_cmds,
        "notes": [
            "This bridge is print-only: it does not call AXLE or write files.",
            "Run lint → attest → (Brockian.lean import) → gen_registry → settle.",
            "Dual-race: prove AND refute both verify ⇒ settle verdict=BLOCKED.",
            "Theorem-level PROVED lives in registry/theorems.json; problem-level "
            "REFUTED/PROVED is pipeline/ledger via pipeline_cli attempt.",
            "SAIR Stage 2: treat Lean proof or finite counterexample as the certificate; "
            "use settle --refute for the counterexample leg.",
        ],
    }


def render_text(plan: dict[str, Any]) -> str:
    lines = [
        f"# formalize→verify plan for {plan['lean_path']}",
        f"# namespace={plan['namespace']}  decls={plan['n_names']}  env={plan['env']}",
        f"# attestation → {plan['attestation_out']}",
        f"# certificate  → {plan['certificate_out']}",
        f"# {plan['import_hint']}",
        "",
        "# --- local / network steps (run in order) ---",
    ]
    for i, c in enumerate(plan["commands"], 1):
        lines.append(f"# {i}. {c['step']}: {c['why']}")
        lines.append(c["cmd"])
        lines.append("")
    if plan["pipeline_commands"]:
        lines.append("# --- pipeline ledger (pick proved OR refuted after settle) ---")
        for c in plan["pipeline_commands"]:
            lines.append(f"# {c['step']}: {c['why']}")
            lines.append(c["cmd"])
            lines.append("")
    lines.append("# notes:")
    for n in plan["notes"]:
        lines.append(f"# - {n}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Print attest + gen_registry (+ settle/pipeline) commands; never calls AXLE."
    )
    ap.add_argument("lean_path", help="path to .lean module (e.g. Brockian/Foo.lean)")
    ap.add_argument(
        "names",
        nargs="*",
        help="declaration short-names (default: discover all theorem/lemma/def in file)",
    )
    ap.add_argument("--namespace", default=None, help="Lean namespace (default: discover)")
    ap.add_argument("--env", default=DEFAULT_ENV)
    ap.add_argument(
        "--refute",
        default=None,
        help="path to negation / counterexample .lean (for settle dual-race)",
    )
    ap.add_argument(
        "--pipeline-id",
        default=None,
        help="problem card id (e.g. distill-etp-stage2) for pipeline attempt commands",
    )
    ap.add_argument(
        "--no-settle",
        action="store_true",
        help="omit settle.py command from the plan",
    )
    ap.add_argument("--json", action="store_true", help="emit plan as JSON")
    args = ap.parse_args(argv)

    if not os.path.exists(args.lean_path):
        print(f"error: no such file: {args.lean_path}", file=sys.stderr)
        return 2

    ns = infer_namespace(args.lean_path, args.namespace)
    plan = build_plan(
        lean_path=args.lean_path,
        names=list(args.names),
        namespace=ns,
        env=args.env,
        refute=args.refute,
        pipeline_id=args.pipeline_id,
        include_settle=not args.no_settle,
    )
    if args.json:
        print(json.dumps(plan, indent=2))
    else:
        print(render_text(plan), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
