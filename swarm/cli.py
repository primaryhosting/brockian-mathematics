from __future__ import annotations

import argparse
import json

from .program import load, validate
from .store import EvidenceStore


def main() -> int:
    parser = argparse.ArgumentParser(prog="brockian-swarm")
    sub = parser.add_subparsers(dest="command", required=True)
    check = sub.add_parser("program-check")
    check.add_argument("manifest")
    init = sub.add_parser("program-init")
    init.add_argument("manifest")
    init.add_argument("--store", default=".swarm")
    audit = sub.add_parser("evidence-audit")
    audit.add_argument("--store", default=".swarm")
    args = parser.parse_args()
    if args.command in {"program-check", "program-init"}:
        tasks = load(args.manifest)
        errors = validate(tasks)
        if errors:
            print(json.dumps({"ok": False, "errors": errors}, indent=2)); return 1
        if args.command == "program-init":
            store = EvidenceStore(args.store)
            for task in tasks:
                store.append("task.declared", task.to_dict())
        print(json.dumps({"ok": True, "tasks": len(tasks),
                          "unlocked": sum(t.unlocked for t in tasks)}, indent=2)); return 0
    errors = EvidenceStore(args.store).verify()
    print(json.dumps({"ok": not errors, "errors": errors}, indent=2))
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
