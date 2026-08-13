#!/usr/bin/env python3
"""Deterministic proof identity helpers used by the harvest and audit pipeline.

Job IDs and target labels are provenance, not proof identity.  This module records
both exact/normalized source hashes and normalized declaration-signature hashes so
duplicate attempts can be reconciled without conflating similarly named theorems.
"""
from __future__ import annotations

import hashlib
import pathlib
import re
from typing import Iterable

DECL = re.compile(
    r"(?m)^\s*(?:protected\s+)?(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
BOUNDARY = re.compile(
    r"(?m)^\s*(?:(?:protected\s+)?(?:theorem|lemma|def|abbrev|instance|example)\b|"
    r"namespace\b|section\b|end\b)"
)
NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$")
END = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*(?:--.*)?$")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def normalize_source(text: str) -> str:
    """Normalize only transport trivia; do not rewrite Lean syntax."""
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return "\n".join(line.rstrip() for line in text.splitlines()).strip() + "\n"


def source_hashes(text: str) -> dict[str, str]:
    return {
        "source_sha256": sha256_text(text),
        "normalized_source_sha256": sha256_text(normalize_source(text)),
    }


def _namespace_at(text: str, offset: int) -> str:
    stack: list[str] = []
    cursor = 0
    for line in text.splitlines(keepends=True):
        if cursor >= offset:
            break
        match = NAMESPACE.match(line)
        if match:
            stack.append(match.group(1))
        else:
            match = END.match(line)
            if match and stack:
                named = match.group(1)
                if named:
                    while stack:
                        popped = stack.pop()
                        if popped == named or popped.endswith("." + named):
                            break
                else:
                    stack.pop()
        cursor += len(line)
    return ".".join(stack)


def declaration_signatures(text: str) -> list[dict[str, str]]:
    """Extract normalized theorem/lemma headers and their stable hashes.

    This is an audit index, not a Lean parser.  AXLE/local Lean remains authoritative.
    Multiline headers are captured up to ``:=`` (or the next declaration boundary).
    """
    normalized = normalize_source(text)
    matches = list(DECL.finditer(normalized))
    out: list[dict[str, str]] = []
    for index, match in enumerate(matches):
        following = matches[index + 1].start() if index + 1 < len(matches) else len(normalized)
        chunk = normalized[match.start() : following]
        assign = chunk.find(":=")
        if assign >= 0:
            header = chunk[:assign]
        else:
            boundary = BOUNDARY.search(chunk, match.end() - match.start())
            header = chunk[: boundary.start()] if boundary else chunk
        header = re.sub(r"--[^\n]*", " ", header)
        header = re.sub(r"\s+", " ", header).strip()
        namespace = _namespace_at(normalized, match.start())
        short = match.group(2)
        full = short if "." in short or not namespace else f"{namespace}.{short}"
        out.append(
            {
                "kind": match.group(1),
                "name": full,
                "short_name": short.split(".")[-1],
                "signature": header,
                "signature_sha256": sha256_text(header),
            }
        )
    return out


def identity_metadata(text: str) -> dict[str, object]:
    return {**source_hashes(text), "declarations": declaration_signatures(text)}


def target_is_represented(target: str, declarations: Iterable[dict[str, str]]) -> bool:
    short = target.split(".")[-1]
    return any(
        declaration.get("name") == target or declaration.get("short_name") == short
        for declaration in declarations
    )


def safe_stem(target: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", target).strip("_") or "unnamed"


def artifact_filenames(targets: Iterable[str]) -> dict[str, str]:
    groups: dict[str, list[str]] = {}
    for target in sorted(set(targets)):
        groups.setdefault(safe_stem(target), []).append(target)
    result: dict[str, str] = {}
    for stem, members in groups.items():
        for index, target in enumerate(members):
            # Preserve the historical unsuffixed path for the first deterministic
            # member; every additional collision gets an unambiguous hash suffix.
            suffix = "" if index == 0 else "__" + sha256_text(target)[:10]
            result[target] = f"{stem}{suffix}.lean"
    return result


def harvested_source_path(root: pathlib.Path, account: str, project_id: str) -> pathlib.Path | None:
    """Find new full-UUID files first, then legacy 8-character filenames."""
    for name in (f"{account}_{project_id}.lean", f"{account}_{project_id[:8]}.lean"):
        path = root / name
        if path.exists():
            return path
    return None
