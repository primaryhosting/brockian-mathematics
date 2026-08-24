from __future__ import annotations

import json
import pathlib

from .model import Task


def load(path: str | pathlib.Path) -> list[Task]:
    data = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
    return [Task.from_dict(item) for item in data["tasks"]]


def validate(tasks: list[Task]) -> list[str]:
    errors: list[str] = []
    ids = [t.id for t in tasks]
    if len(ids) != len(set(ids)):
        errors.append("duplicate task id")
    known = set(ids)
    for task in tasks:
        missing = set(task.prerequisites) - known
        if missing:
            errors.append(f"{task.id}: unknown prerequisites {sorted(missing)}")
        if not task.statement.strip():
            errors.append(f"{task.id}: empty statement lock")
    return errors
