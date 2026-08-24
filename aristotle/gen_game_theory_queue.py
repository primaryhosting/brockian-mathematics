#!/usr/bin/env python3
"""Generate the reviewable Aristotle queue for the game-theory program.

The source manifest is candidate-only.  This generator emits only entries marked
READY; it does not activate them in night_submit.py or submit anything.
"""
from __future__ import annotations

import json
import pathlib


ROOT = pathlib.Path(__file__).resolve().parent
SOURCE = ROOT / "game_theory_program.json"
OUT = ROOT / "game_theory_queue.json"

REQUIRED = {
    "target",
    "track",
    "phase",
    "rank",
    "difficulty",
    "solver_status",
    "firewall",
    "depends_on",
    "statement",
    "goal",
}


def main() -> None:
    program = json.loads(SOURCE.read_text())
    targets = program["targets"]
    names = [item["target"] for item in targets]
    if len(names) != len(set(names)):
        raise ValueError("duplicate game-theory target")

    known = set(names)
    for item in targets:
        missing = REQUIRED - set(item)
        if missing:
            raise ValueError(f"{item.get('target', '<unnamed>')}: missing {sorted(missing)}")
        unknown = set(item["depends_on"]) - known
        if unknown:
            raise ValueError(f"{item['target']}: unknown dependencies {sorted(unknown)}")

    ready = sorted(
        (item for item in targets if item["solver_status"] == "READY"),
        key=lambda item: (item["phase"], item["rank"], item["target"]),
    )
    queue = [
        {
            "target": item["target"],
            "tier": f"GT-{item['track']}",
            "rank": item["rank"],
            "difficulty": item["difficulty"],
            "goal": item["goal"],
            "statement": item["statement"],
            "program_phase": item["phase"],
            "firewall": item["firewall"],
            "depends_on": item["depends_on"],
            "register": "CANDIDATE_ONLY",
        }
        for item in ready
    ]
    OUT.write_text(json.dumps({"count": len(queue), "queue": queue}, indent=1) + "\n")
    print(f"wrote {OUT} with {len(queue)} reviewable game-theory targets")


if __name__ == "__main__":
    main()
