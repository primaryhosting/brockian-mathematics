from pathlib import Path

import pytest

from scripts.check_lean_modules import dependency_order, local_imports


def write(root: Path, relative: str, source: str) -> Path:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_dependency_order_is_transitive_stable_and_unique(tmp_path: Path) -> None:
    base = write(tmp_path, "Brockian/Base.lean", "import Mathlib\n")
    left = write(tmp_path, "Brockian/Left.lean", "import Brockian.Base\n")
    right = write(tmp_path, "Brockian/Right.lean", "import Brockian.Base\n")
    goal = write(
        tmp_path,
        "Brockian/Goal.lean",
        "import Brockian.Left\nimport Brockian.Right\n",
    )

    assert dependency_order([goal], tmp_path) == [base, left, right, goal]


def test_missing_local_import_fails_closed(tmp_path: Path) -> None:
    goal = write(tmp_path, "Brockian/Goal.lean", "import Brockian.Missing\n")

    with pytest.raises(FileNotFoundError, match="imports missing local module"):
        local_imports(goal, tmp_path)


def test_cycle_is_reported(tmp_path: Path) -> None:
    left = write(tmp_path, "Brockian/Left.lean", "import Brockian.Right\n")
    write(tmp_path, "Brockian/Right.lean", "import Brockian.Left\n")

    with pytest.raises(ValueError, match="local Lean import cycle"):
        dependency_order([left], tmp_path)
