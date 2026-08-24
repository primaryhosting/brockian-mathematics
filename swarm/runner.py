from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Callable

from .model import Candidate, Task
from .planner import assignments
from .prompts import render
from .store import EvidenceStore

Agent = Callable[[str], str]


class SwarmRunner:
    def __init__(self, store: EvidenceStore, agents: dict[str, Agent], workers: int = 4):
        self.store, self.agents, self.workers = store, agents, workers

    def run(self, task: Task) -> list[Candidate]:
        self.store.append("task.locked", task.to_dict())
        jobs = [(role, self.agents[role], render(task, role))
                for _, role in assignments(task) if role in self.agents]
        candidates: list[Candidate] = []
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            futures = {pool.submit(agent, prompt): role for role, agent, prompt in jobs}
            for future in as_completed(futures):
                role = futures[future]
                try:
                    candidate = Candidate(task.id, role, future.result(), role)
                    self.store.append("candidate.received", candidate.__dict__)
                    candidates.append(candidate)
                except Exception as exc:  # noqa: BLE001
                    self.store.append("candidate.failed", {"task_id": task.id, "role": role,
                                                           "error": str(exc)})
        return candidates
