from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import StrEnum
from typing import Any


class ClaimKind(StrEnum):
    PROVE = "prove"
    REFUTE = "refute"
    GENERALIZE = "generalize"
    EXPLAIN = "explain"
    COMPUTE = "compute"


class TaskStatus(StrEnum):
    PLANNED = "planned"
    SUBMITTED = "submitted"
    CANDIDATE = "candidate"
    REJECTED = "rejected"
    VERIFIED = "verified"


class Gate(StrEnum):
    STATEMENT = "statement_lock"
    SOURCE = "source_integrity"
    COMPILE = "lean_compile"
    AXIOMS = "axiom_audit"
    EVIDENCE = "evidence_integrity"


@dataclass(frozen=True)
class Task:
    id: str
    module: str
    declaration: str
    statement: str
    kind: ClaimKind = ClaimKind.PROVE
    prerequisites: tuple[str, ...] = ()
    roles: tuple[str, ...] = ("prover", "skeptic", "explainer")
    unlocked: bool = True
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        data = asdict(self)
        data["kind"] = self.kind.value
        return data

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "Task":
        return cls(
            id=data["id"], module=data["module"], declaration=data["declaration"],
            statement=data["statement"], kind=ClaimKind(data.get("kind", "prove")),
            prerequisites=tuple(data.get("prerequisites", ())),
            roles=tuple(data.get("roles", ("prover", "skeptic", "explainer"))),
            unlocked=bool(data.get("unlocked", True)), metadata=data.get("metadata", {}),
        )


@dataclass(frozen=True)
class Candidate:
    task_id: str
    role: str
    content: str
    provider: str
    remote_id: str | None = None


@dataclass(frozen=True)
class GateResult:
    gate: Gate
    passed: bool
    detail: str
