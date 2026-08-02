"""Problem card load / validate / save."""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Optional

DOMAINS = ("erdos", "distillation", "sair", "math", "physics", "cs", "quantum")
STATUSES = (
    "open",
    "partial",
    "scaffolded",
    "conditional",
    "proved",
    "refuted",
    "distilled",
    "blocked",
    "literature",
)
BACKENDS = (
    "lean_axle",
    "literature",
    "compute",
    "distillation_harness",
    "hybrid",
)
ATTACK_MODES = (
    "literature",
    "formalize",
    "refute",
    "compute",
    "distill",
    "decompose",
    "dual_prover",
)

# Pipeline root: pipeline/
PIPELINE_ROOT = Path(__file__).resolve().parents[1]
CATALOG_ROOT = PIPELINE_ROOT / "catalog"
SCHEMA_PATH = PIPELINE_ROOT / "schema" / "problem.schema.json"


@dataclass
class ProblemCard:
    id: str
    domain: str
    title: str
    statement: str
    status: str = "open"
    source: dict[str, Any] = field(default_factory=dict)
    difficulty: int = 3
    tags: list[str] = field(default_factory=list)
    formal_targets: list[dict[str, Any]] = field(default_factory=list)
    attack_modes: list[str] = field(default_factory=list)
    verification: dict[str, Any] = field(default_factory=dict)
    risk_tier: int = 1
    notes: str = ""
    attempts: list[dict[str, Any]] = field(default_factory=list)
    ledger_refs: list[str] = field(default_factory=list)
    priority: int = 50

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "ProblemCard":
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        filtered = {k: v for k, v in data.items() if k in known}
        return cls(**filtered)


def validate_card(data: dict[str, Any]) -> list[str]:
    """Lightweight validation (no jsonschema dependency required). Returns error strings."""
    errs: list[str] = []
    for key in ("id", "domain", "title", "statement", "status", "verification"):
        if key not in data or data[key] in (None, ""):
            errs.append(f"missing required field: {key}")
    if "domain" in data and data["domain"] not in DOMAINS:
        errs.append(f"invalid domain: {data.get('domain')}")
    if "status" in data and data["status"] not in STATUSES:
        errs.append(f"invalid status: {data.get('status')}")
    ver = data.get("verification") or {}
    if isinstance(ver, dict):
        backend = ver.get("backend")
        if backend not in BACKENDS:
            errs.append(f"invalid verification.backend: {backend}")
    else:
        errs.append("verification must be an object")
    diff = data.get("difficulty")
    if diff is not None and (not isinstance(diff, int) or not 1 <= diff <= 5):
        errs.append("difficulty must be int 1..5")
    tier = data.get("risk_tier", 1)
    if not isinstance(tier, int) or not 1 <= tier <= 3:
        errs.append("risk_tier must be int 1..3")
    for mode in data.get("attack_modes") or []:
        if mode not in ATTACK_MODES:
            errs.append(f"invalid attack_mode: {mode}")
    pid = data.get("id", "")
    if isinstance(pid, str) and (len(pid) < 2 or not pid[0].isalnum()):
        errs.append(f"invalid id: {pid}")
    return errs


def load_card(path: Path | str) -> ProblemCard:
    path = Path(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    errs = validate_card(data)
    if errs:
        raise ValueError(f"{path}: " + "; ".join(errs))
    return ProblemCard.from_dict(data)


def save_card(card: ProblemCard, path: Optional[Path | str] = None) -> Path:
    if path is None:
        path = CATALOG_ROOT / card.domain / f"{card.id}.json"
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = card.to_dict()
    errs = validate_card(data)
    if errs:
        raise ValueError(f"cannot save invalid card: " + "; ".join(errs))
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return path


def load_catalog(
    domain: Optional[str] = None,
    status: Optional[str] = None,
    catalog_root: Optional[Path] = None,
) -> list[ProblemCard]:
    root = Path(catalog_root) if catalog_root else CATALOG_ROOT
    cards: list[ProblemCard] = []
    domains = [domain] if domain else list(DOMAINS)
    for d in domains:
        dpath = root / d
        if not dpath.is_dir():
            continue
        for fp in sorted(dpath.glob("*.json")):
            try:
                card = load_card(fp)
            except (ValueError, json.JSONDecodeError) as e:
                raise ValueError(f"bad card {fp}: {e}") from e
            if status and card.status != status:
                continue
            cards.append(card)
    return cards


def find_card(problem_id: str, catalog_root: Optional[Path] = None) -> tuple[ProblemCard, Path]:
    root = Path(catalog_root) if catalog_root else CATALOG_ROOT
    for d in DOMAINS:
        candidate = root / d / f"{problem_id}.json"
        if candidate.is_file():
            return load_card(candidate), candidate
    # allow id that already includes domain prefix mismatch: scan all
    for card in load_catalog(catalog_root=root):
        if card.id == problem_id:
            path = root / card.domain / f"{card.id}.json"
            return card, path
    raise FileNotFoundError(f"problem not found: {problem_id}")
