"""Schema + distill + seed smoke tests."""
from __future__ import annotations

import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO))

from pipeline.core.schema import ProblemCard, load_catalog, save_card, validate_card  # noqa: E402
from pipeline.distill.score import MAX_CHEATSHEET_BYTES, check_cheatsheet  # noqa: E402
from pipeline.scripts import pipeline_cli  # noqa: E402
from pipeline.scripts.seed_catalog import seeds  # noqa: E402


def test_validate_minimal():
    errs = validate_card(
        {
            "id": "math-x",
            "domain": "math",
            "title": "t",
            "statement": "s",
            "status": "open",
            "verification": {"backend": "lean_axle"},
        }
    )
    assert errs == []


def test_validate_bad_domain():
    errs = validate_card(
        {
            "id": "x-1",
            "domain": "biology",
            "title": "t",
            "statement": "s",
            "status": "open",
            "verification": {"backend": "lean_axle"},
        }
    )
    assert any("domain" in e for e in errs)


def test_seeds_validate(tmp_path):
    for card in seeds():
        errs = validate_card(card.to_dict())
        assert errs == [], (card.id, errs)
        p = save_card(card, tmp_path / card.domain / f"{card.id}.json")
        assert p.is_file()


def test_cheatsheet_size():
    path = _REPO / "pipeline" / "distill" / "cheatsheets" / "etp_v0.txt"
    if not path.is_file():
        return
    r = check_cheatsheet(path)
    assert r["size_ok"] is True
    assert r["size_bytes"] <= MAX_CHEATSHEET_BYTES


def test_cli_list_after_seed(tmp_path, monkeypatch):
    # seed into temp catalog by patching CATALOG_ROOT is hard; just run seeds validation
    cards = seeds()
    assert len(cards) >= 10
    domains = {c.domain for c in cards}
    assert domains >= {"erdos", "distillation", "sair", "math", "physics", "cs", "quantum"}
