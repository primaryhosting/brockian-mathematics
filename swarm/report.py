from __future__ import annotations

from collections import Counter

from .model import GateResult, Task


def markdown(task: Task, gates: list[GateResult]) -> str:
    passed = all(g.passed for g in gates) and bool(gates)
    rows = "\n".join(f"| {g.gate.value} | {'PASS' if g.passed else 'FAIL'} | {g.detail} |" for g in gates)
    return (f"# {task.id}\n\nStatus: **{'VERIFIED CANDIDATE' if passed else 'NOT VERIFIED'}**\n\n"
            "| Gate | Result | Detail |\n|---|---|---|\n" + rows + "\n")


def summary(events: list[dict]) -> dict[str, int]:
    return dict(Counter(e["event"] for e in events))
