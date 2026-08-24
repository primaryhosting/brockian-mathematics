from __future__ import annotations

from .model import Task


ROLE_RULES = {
    "prover": "Produce the smallest axiom-clean Lean proof. Preserve the statement exactly.",
    "refuter": "Search for a concrete counterexample. Never call computation a proof.",
    "generalizer": "Identify the weakest hypotheses and a strictly stronger reusable theorem.",
    "skeptic": "Attack definitions, quantifiers, imports, hidden axioms, and novelty claims.",
    "explainer": "Explain the mathematical mechanism and formal proof without overclaiming.",
}


def render(task: Task, role: str) -> str:
    return f"""You are the {role} in an independently checked mathematics campaign.
{ROLE_RULES.get(role, ROLE_RULES['skeptic'])}

TASK ID: {task.id}
MODULE: {task.module}
DECLARATION: {task.declaration}
KIND: {task.kind.value}
STATEMENT LOCK (byte-for-byte semantic target):
{task.statement}

Return JSON with keys: status, analysis, lean_source, counterexample, explanation.
Use status=candidate only for a checkable artifact. Never claim verified/proved: only the verifier may.
"""
