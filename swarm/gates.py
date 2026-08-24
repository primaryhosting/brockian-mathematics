from __future__ import annotations

import pathlib
import re
import subprocess

from engine.verify import ALLOWED_AXIOMS, axiom_audit
from .model import Gate, GateResult, Task


HOLE = re.compile(r"\b(sorry|admit|native_decide)\b")


def statement_gate(task: Task, source: str) -> GateResult:
    compact, target = " ".join(source.split()), " ".join(task.statement.split())
    return GateResult(Gate.STATEMENT, target in compact,
                      "locked statement found" if target in compact else "statement drift")


def source_gate(source: str) -> GateResult:
    match = HOLE.search(source)
    return GateResult(Gate.SOURCE, match is None,
                      "no forbidden placeholders" if match is None else f"forbidden token: {match.group(1)}")


def local_compile(path: str, timeout: int = 600) -> GateResult:
    try:
        proc = subprocess.run(["lake", "env", "lean", path], text=True,
                              capture_output=True, timeout=timeout, check=False)
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        return GateResult(Gate.COMPILE, False, f"local verifier unavailable: {exc}")
    detail = "Lean accepted source" if proc.returncode == 0 else (proc.stderr or proc.stdout)[-500:]
    return GateResult(Gate.COMPILE, proc.returncode == 0, detail)


def axle_gate(source: str) -> GateResult:
    result = axiom_audit(source)
    passed = result.get("trusted") is True and set(result.get("axioms", ())) <= ALLOWED_AXIOMS
    return GateResult(Gate.AXIOMS, passed, result.get("detail") or
                      f"axioms={result.get('axioms', [])}; environment={result.get('environment')}")


def verify_candidate(task: Task, source: str, path: str | None = None,
                     use_axle: bool = False) -> list[GateResult]:
    results = [statement_gate(task, source), source_gate(source)]
    if path:
        pathlib.Path(path).write_text(source, encoding="utf-8")
        results.append(local_compile(path))
    if use_axle:
        results.append(axle_gate(source))
    return results
