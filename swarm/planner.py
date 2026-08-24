from __future__ import annotations

from .model import Task


DEFAULT_ROLES = ("prover", "refuter", "generalizer", "skeptic", "explainer")


def ready(tasks: list[Task], verified: set[str]) -> list[Task]:
    return [t for t in tasks if t.unlocked and set(t.prerequisites) <= verified]


def assignments(task: Task) -> list[tuple[Task, str]]:
    return [(task, role) for role in (task.roles or DEFAULT_ROLES)]
