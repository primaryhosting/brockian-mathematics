"""Distillation challenge gates: size limit + optional accuracy stub."""
from __future__ import annotations

from pathlib import Path
from typing import Any, Optional

# SAIR Stage 1: cheatsheet ≤ 10 kilobytes
MAX_CHEATSHEET_BYTES = 10 * 1024


def check_cheatsheet(
    path: Path | str,
    max_bytes: int = MAX_CHEATSHEET_BYTES,
    accuracy: Optional[float] = None,
    min_accuracy: Optional[float] = None,
) -> dict[str, Any]:
    path = Path(path)
    if not path.is_file():
        return {
            "ok": False,
            "path": str(path),
            "error": "file not found",
            "size_bytes": 0,
            "max_bytes": max_bytes,
        }
    raw = path.read_bytes()
    size = len(raw)
    size_ok = size <= max_bytes
    acc_ok = True
    if min_accuracy is not None:
        if accuracy is None:
            acc_ok = False
        else:
            acc_ok = accuracy >= min_accuracy

    return {
        "ok": size_ok and acc_ok,
        "path": str(path),
        "size_bytes": size,
        "max_bytes": max_bytes,
        "size_ok": size_ok,
        "accuracy": accuracy,
        "min_accuracy": min_accuracy,
        "accuracy_ok": acc_ok,
        "head_preview": raw[:200].decode("utf-8", errors="replace"),
    }
