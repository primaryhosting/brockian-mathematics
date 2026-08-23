"""Render deterministic, provenance-safe task packets for the geometry swarm.

This script deliberately plans work; it does not infer a theorem or promote any
task to the registry. The validator runs first so malformed or novelty-claiming
benchmark data cannot be dispatched.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import yaml

import validate_geometry_swarm as validator


DEFAULT_PATH = validator.DEFAULT_PATH


def load_benchmark(path: Path = DEFAULT_PATH) -> dict[str, Any]:
    errors = validator.validate_path(path)
    if errors:
        raise ValueError("\n".join(errors))
    document = yaml.safe_load(path.read_text(encoding="utf-8"))
    assert isinstance(document, dict)
    return document


def task_packet(document: dict[str, Any], track: dict[str, Any]) -> dict[str, Any]:
    contracts = document["stage_contracts"]
    return {
        "benchmark_id": document["benchmark_id"],
        "track_id": track["id"],
        "priority": track["priority"],
        "classification": track["classification"],
        "novelty_ledger": False,
        "source_anchors": track["source_anchors"],
        "target": track["target"],
        "required_assumptions": track["required_assumptions"],
        "adversarial_cases": track["adversarial_cases"],
        "baseline": track.get("existing_baseline", {}),
        "tasks": [
            {
                "stage": stage,
                "role": contracts[stage]["role"],
                "required_output": contracts[stage]["required_output"],
            }
            for stage in document["stages"]
        ],
        "promotion_gate": (
            "No promotion from this packet: a new theorem requires a Lean source, clean build, "
            "independent verification, registry derivation, and a separate provenance verdict."
        ),
    }


def render_markdown(packet: dict[str, Any]) -> str:
    lines = [
        f"# {packet['track_id']}",
        "",
        f"Priority: {packet['priority']}  ",
        f"Classification: {packet['classification']}  ",
        "Novelty ledger: excluded",
        "",
        "## Target",
        "",
        packet["target"],
        "",
        "## Required assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in packet["required_assumptions"])
    lines.extend(["", "## Adversarial cases", ""])
    lines.extend(f"- {item}" for item in packet["adversarial_cases"])
    lines.extend(["", "## Stage packets", ""])
    for task in packet["tasks"]:
        lines.extend([f"### {task['stage']} - {task['role']}", "", task["required_output"], ""])
    lines.extend(["## Promotion gate", "", packet["promotion_gate"], ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--path", type=Path, default=DEFAULT_PATH)
    parser.add_argument("--track", help="track id; omit to render all tracks")
    parser.add_argument("--format", choices=("json", "markdown"), default="markdown")
    args = parser.parse_args()
    document = load_benchmark(args.path)
    tracks = document["tracks"]
    if args.track:
        tracks = [track for track in tracks if track["id"] == args.track]
        if not tracks:
            parser.error(f"unknown track: {args.track}")
    packets = [task_packet(document, track) for track in tracks]
    if args.format == "json":
        print(json.dumps(packets, indent=2, sort_keys=True))
    else:
        print("\n".join(render_markdown(packet) for packet in packets))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
